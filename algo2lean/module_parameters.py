"""Small emission helpers for explicitly parameterized module interfaces."""


def emit_dependency_context(module, *, step=True):
    if not module.dependencies:
        return []
    lines = ["variable (dependencies : Dependencies)", ""]
    for name in ["Frame", "Stack", "Configuration", "Transcript"] + (["Step"] if step else []):
        lines.append('local notation "%s" => %s dependencies' % (name, name))
    for slot in module.dependencies.values():
        lines.append('local notation "is_%s" => is_%s dependencies' % (slot.local_name, slot.local_name))
    return lines + [""]
