(function (root, factory) {
  "use strict";
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.Algo2LeanInterface = api;
})(typeof window === "undefined" ? globalThis : window, function () {
  "use strict";

  const GROUPS = [
    { id: "outputs", title: "Outputs", categories: ["output"] },
    { id: "calls", title: "Calls", categories: ["execution", "helper"] },
    { id: "transcripts", title: "Transcripts", categories: ["transcript"] },
    { id: "locations", title: "Named locations and values", categories: ["location", "observation"] },
    { id: "inputs", title: "Inputs", categories: ["input"] },
  ];
  let renderSerial = 0;

  function summaryEntries(fn) {
    if (typeof fn.name !== "string" || !fn.name) return [];
    const entries = [
      { name: fn.output_relation, category: "output", file_kind: "core",
        meaning: "A completed execution returns the stated output from the supplied input." },
      { name: fn.transcript_relation, category: "transcript", file_kind: "core",
        meaning: "A finite sequence of configurations is a valid history from the supplied input. The history may end before the function finishes." },
    ];
    if (fn.cost_relation) entries.push({ name: fn.cost_relation, category: "output", file_kind: "core",
      meaning: "A completed execution returns the stated output and increases the clocks by the stated amounts. The output and costs belong to the same execution." });
    for (const point of Array.isArray(fn.points) ? fn.points : []) {
      if (point && typeof point.relation === "string") entries.push({
        name: point.relation, category: "location", file_kind: "points", line: point.line, column: point.column,
        meaning: "The supplied configuration is at this named location, before its statement executes. This local proposition does not require a transcript or a reachability proof.",
      });
    }
    return entries;
  }

  function normalizeEntries(functions) {
    const entries = [];
    const seen = new Set();
    for (const fn of Array.isArray(functions) ? functions : []) {
      if (!fn || typeof fn !== "object") continue;
      const raw = Array.isArray(fn.interface_entries) ? fn.interface_entries : summaryEntries(fn);
      for (const entry of raw) {
        if (!entry || typeof entry.name !== "string" || !entry.name) continue;
        if (/(?:^|\.)(?:is_(?:OutputWithCost|Output|Execution|SummaryFrom|Summary|HeapTranscript|Transcript)_|At_|local_|element_|validInputs_|initial_|load_)[^.]+(?:\.(?:output|withCost|execution|eq_of_summary))?$/.test(entry.name)) continue;
        const fileKind = ["core", "points", "facts"].includes(entry.file_kind) ? entry.file_kind : "core";
        const key = `${fileKind}:${entry.name}`;
        if (seen.has(key)) continue;
        seen.add(key);
        const category = GROUPS.some((group) => group.categories.includes(entry.category)) ? entry.category : "helper";
        entries.push({
          name: entry.name,
          category,
          signature: typeof entry.signature === "string" && entry.signature ? entry.signature : null,
          meaning: typeof entry.meaning === "string" ? entry.meaning : "Inspect the generated declaration for this interface.",
          arguments: (Array.isArray(entry.arguments) ? entry.arguments : [])
            .filter((argument) => argument && typeof argument.name === "string")
            .map((argument) => ({ name: argument.name,
              type: typeof argument.type === "string" ? argument.type : null,
              meaning: typeof argument.meaning === "string" ? argument.meaning : "",
              implicit: argument.implicit === true, anonymous: argument.anonymous === true })),
          file_kind: fileKind,
          line: Number.isInteger(entry.line) && entry.line > 0 ? entry.line : null,
          column: Number.isInteger(entry.column) && entry.column > 0 ? entry.column : 1,
        });
      }
    }
    return entries;
  }

  function groupEntries(entries) {
    return GROUPS.map((group) => ({ id: group.id, title: group.title,
      entries: entries.filter((entry) => group.categories.includes(entry.category)) }))
      .filter((group) => group.entries.length);
  }

  function render(container, functions, options = {}) {
    const document = options.document || container.ownerDocument;
    const prefix = `algo-interface-${++renderSerial}`;
    const entries = normalizeEntries(functions);
    const files = { core: options.generatedFile || "Algorithm definitions",
      points: options.pointsFile || "Named-line interface", facts: options.factsFile || "Generated facts" };
    let expanded = null;
    let entrySerial = 0;

    function element(tag, className, text) {
      const node = document.createElement(tag);
      if (className) node.className = className;
      if (text !== undefined) node.textContent = text;
      return node;
    }

    function close(focus = false) {
      if (!expanded) return;
      const previous = expanded;
      previous.panel.hidden = true;
      previous.button.setAttribute("aria-expanded", "false");
      previous.wrapper.className = "interface-entry";
      expanded = null;
      if (focus) previous.button.focus();
    }

    container.replaceChildren();
    for (const group of groupEntries(entries)) {
      const section = element("details", "interface-group");
      section.open = group.id === "outputs";
      const heading = element("summary", "interface-group-title", group.title);
      heading.id = `${prefix}-${group.id}`;
      section.setAttribute("aria-labelledby", heading.id);
      const list = element("div", "interface-entries");
      section.append(heading, list);
      for (const entry of group.entries) {
        const id = `${prefix}-entry-${entrySerial++}`;
        const wrapper = element("div", "interface-entry");
        const button = element("button", "interface-button", entry.name);
        button.type = "button";
        button.id = `${id}-button`;
        button.setAttribute("aria-expanded", "false");
        button.setAttribute("aria-controls", `${id}-spec`);
        const panel = element("div", "interface-spec");
        panel.id = `${id}-spec`;
        panel.hidden = true;
        panel.setAttribute("role", "region");
        panel.setAttribute("aria-labelledby", button.id);
        const signature = element("pre", "interface-signature");
        signature.append(element("code", "", entry.signature || entry.name));
        panel.append(signature, element("p", "interface-meaning", entry.meaning));
        if (!entry.signature) panel.append(element("p", "interface-unavailable",
          "This compiler did not provide a signature. Inspect the declaration in the generated file for its exact arguments and types."));
        if (entry.arguments.length) {
          const argumentsList = element("dl", "interface-arguments");
          for (const argument of entry.arguments) {
            const name = element("dt", "interface-argument-name");
            const binding = argument.name + (argument.type ? ` : ${argument.type}` : "");
            name.append(element("code", "", argument.implicit ? `{${binding}}` : binding));
            if (argument.anonymous) name.append(element("span", "", " (positional argument)"));
            argumentsList.append(name, element("dd", "", argument.meaning));
          }
          panel.append(argumentsList);
        }
        const file = element("p", "interface-file");
        file.append(element("span", "", "Defined in "), element("code", "", files[entry.file_kind]));
        panel.append(file);
        if (entry.category === "location" && entry.line && typeof options.goToSource === "function") {
          const source = element("button", "interface-source-button", `Go to source · line ${entry.line}`);
          source.type = "button";
          source.addEventListener("click", () => options.goToSource(entry.line, entry.column));
          panel.append(source);
        }
        button.addEventListener("click", () => {
          if (expanded?.button === button) { close(); return; }
          close();
          panel.hidden = false;
          button.setAttribute("aria-expanded", "true");
          wrapper.className = "interface-entry is-open";
          expanded = { button, panel, wrapper };
        });
        panel.addEventListener("keydown", (event) => {
          if (event.key === "Escape") { event.preventDefault(); close(true); }
        });
        wrapper.append(button, panel);
        list.append(wrapper);
      }
      container.append(section);
    }
    const missing = !entries.length && Array.isArray(functions) && functions.some((fn) => fn && typeof fn.name === "string");
    if (missing) container.append(element("p", "interface-unavailable",
      "Interface metadata is unavailable. Restart the editor server with the current compiler."));
    container.hidden = !entries.length && !missing;
    return { entries, close };
  }

  return { normalizeEntries, groupEntries, render };
});
