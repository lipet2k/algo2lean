"""Optional parallel contracts over independently compiled source modules."""

import ast
import copy

from .parallel import emit_parallel, parallel_functions, require_parallel
from .publication import credit_generated


def adapt_imported_forks(tree, external):
    """Give an imported fork child a typed local return boundary.

    One tiny ordinary forwarding function per imported child reuses the existing
    call and fork rules. Its body delegates; imported instructions are never
    copied. All original fork arguments are still captured before either child.
    """
    adapters = {}
    occupied = {node.name for node in tree.body if isinstance(node, (ast.FunctionDef, ast.ClassDef))}
    for node in list(ast.walk(tree)):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "fork_join"):
            continue
        for child in node.args:
            if not (isinstance(child, ast.Call) and isinstance(child.func, ast.Name)
                    and child.func.id in external):
                continue
            callee = child.func.id
            if callee not in adapters:
                function = external[callee]
                name = "_a2l_parallel_" + callee
                while name in occupied:
                    name += "_"
                occupied.add(name)
                wrapper = copy.deepcopy(function.node)
                wrapper.name = name
                wrapper.decorator_list = []
                wrapper.body = [ast.Return(value=ast.Call(func=ast.Name(id=callee, ctx=ast.Load()),
                    args=[ast.Name(id=arg, ctx=ast.Load()) for arg, _ in function.parameters], keywords=[]))]
                wrapper.parallel_adapter = True
                ast.copy_location(wrapper, node)
                ast.fix_missing_locations(wrapper)
                tree.body.append(wrapper)
                adapters[callee] = name
            child.func.id = adapters[callee]


def attach_parallel(compilation, *, force=False):
    units = list(compilation.implementation_modules.values()) + [
        module for module in compilation.modules.values() if module.implementation is None]
    if not force and not any(lowerer.forks for module in units for lowerer in module.lowered.values()):
        return
    completed = set()

    def require(module, admitted):
        missing = next((name for name, lowerer in module.lowered.items()
                        if lowerer.forks and name not in admitted), None)
        if missing is None:
            return
        from .frontend import CompileError
        from .project import ProjectError
        owner = compilation.project.modules.get(module.name)
        if owner is None:
            facade = next(candidate for candidate in compilation.modules.values()
                          if candidate.implementation is module
                          and missing in candidate.implementation_names.values())
            owner = compilation.project.modules[facade.name]
        try:
            require_parallel(module.lowered, admitted)
        except CompileError as error:
            raise ProjectError(error.message, owner.path, error.line, error.column) from None

    def visit(module):
        if module.name in completed:
            return
        completed.add(module.name)
        if module.implementation is not None:
            visit(module.implementation)
            source = module.implementation
            module.parallel_functions = {name for name, internal in module.implementation_names.items()
                                         if internal in source.parallel_functions}
            if not source.parallel_lean:
                return
            module.parallel_module = "Algo." + module.name + ".Parallel"
            lines = ["import " + module.lean_module, "import " + source.parallel_module,
                     "", "namespace " + module.namespace, "", "namespace Algo2LeanGenerated"]
            for name in ("parallelNext", "parallelSimulation"):
                lines += ["abbrev %s := @%s.Algo2LeanGenerated.%s" % (name, source.namespace, name)]
            lines += ["end Algo2LeanGenerated", ""]
            from .public_names import function_namespace
            for name, internal in module.implementation_names.items():
                if name in module.parallel_functions:
                    public = function_namespace(module.functions[name])
                    original = source.namespace + "." + function_namespace(source.functions[internal])
                    for member in ("ParallelCall", "ParallelCall.call"):
                        lines += ["abbrev %s.%s := @%s.%s" % (public, member, original, member)]
            module.parallel_lean = credit_generated("\n".join(lines + ["", "end " + module.namespace, ""]))
            return
        if module.dependencies or module.environments or any(call.interface_code for call in module.imports.values()):
            require(module, set())
            return
        for call in module.imports.values():
            dependency = compilation.modules[call.module]
            visit(dependency)
            call.parallel_supported = call.name in (dependency.implementation or dependency).parallel_functions
        module.parallel_functions = parallel_functions(module.lowered, module.imports)
        require(module, module.parallel_functions)
        if not module.parallel_functions:
            return
        module.parallel_module = "Algo." + module.name + ".Parallel"
        dependencies = dict.fromkeys(call.module for call in module.imports.values() if call.parallel_supported)
        lines = ["import " + module.lean_module, "import Algo2LeanLib.ParallelModules"]
        lines += ["import Algo." + name + ".Parallel" for name in dependencies]
        lines += ["", "namespace " + module.namespace,
                  "open _root_.Algo2LeanGenerated Algo2LeanGenerated", ""]
        emit_parallel(lines, module.lowered, module.namespace, module.imports, module.parallel_functions)
        module.parallel_lean = credit_generated("\n".join(lines + ["end " + module.namespace, ""]))

    for module in compilation.modules.values():
        visit(module)
