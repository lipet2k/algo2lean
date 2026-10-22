// Filename, module, and starter-analysis conventions shared by the editor store.
export function safeFilename(value, extension) {
  const base = value.trim().split(/[\\/]/).pop().replace(/[<>:"|?*\u0000-\u001f]/g, "_") || "untitled";
  return base.replace(/\.(algo|lean)$/i, "") + extension;
}

export function moduleForFilename(name) {
  const basename = name.split(/[\\/]/).pop().replace(/\.[^.]*$/, "");
  const words = basename.match(/[A-Za-z0-9]+/g) || [];
  let module = words.map((word) => word[0].toUpperCase() + word.slice(1)).join("");
  if (!module || /^\d/.test(module)) module = "Algorithm" + module;
  return module + "Generated";
}

export function starterAnalysis(module, includeFacts = true) {
  if (module.startsWith("Algo.") && module.endsWith(".Generated")) {
    const prefix = module.slice(0, -10);
    const namespace = prefix.split(".").map((part) => `«${part}»`).join(".");
    const factsImport = includeFacts ? `import ${prefix}.Facts\n` : "";
    const helpers = includeFacts ? "Points and Facts are optional when the proof does not use their helpers." : "Points adds named locations and local values; omit this import if unused.";
    return `import ${module}\nimport ${prefix}.Points\n${factsImport}\nopen Algo2LeanCore _root_.Algo2LeanGenerated\nopen ${namespace} ${namespace}.Algo2LeanGenerated\n\n-- State output theorems using the public relations shown by the compiler.\n-- Use the generated call interface for guarantees reusable by other algorithms.\n-- Import Algo.<module>.Analysis to reuse a companion proof.\n-- ${helpers}\n`;
  }
  return `import ${module}\nimport ${module}Points\n\nopen Algo2LeanCore Algo2LeanGenerated\n\n-- State output theorems using the public relations shown by the compiler.\n-- Use the generated call interface for guarantees reusable by other algorithms.\n-- Points adds named locations and local values; omit this import if unused.\n`;
}

export function analysisForExample(example, module) {
  if (typeof example?.analysis !== "string") return starterAnalysis(module);
  if (!example.module || example.module === module) return example.analysis;
  return example.analysis.replace(new RegExp(`^import ${example.module}(Points)?[ \\t]*$`, "gm"),
    (_, points) => `import ${module}${points || ""}`);
}

export function projectModule(path) {
  return `Algo.${path.slice(0, -5).replace(/\//g, ".")}`;
}

export function validProjectPath(path, extension) {
  if (typeof path !== "string" || !path.endsWith(extension) || path.length > 255) return false;
  return path.slice(0, -extension.length).split("/").every((part) => /^[A-Za-z_][A-Za-z_0-9]*$/.test(part));
}

export function leanPath(module, inProject) {
  return `${inProject ? module.replace(/\./g, "/") : module}.lean`;
}
