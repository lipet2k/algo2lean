(function (root, factory) {
  "use strict";
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.Algo2LeanProofOutline = api;
})(typeof window === "undefined" ? globalThis : window, function () {
  "use strict";

  // This scanner provides source navigation, not Lean elaboration. Mask comments
  // and literals without changing offsets so quoted declarations cannot become links.
  function scan(source) {
    const chars = source.split("");
    const comments = [];
    const literals = [];
    const blank = (start, end) => {
      for (let j = start; j < end; j++) if (chars[j] !== "\n" && chars[j] !== "\r") chars[j] = " ";
    };
    for (let i = 0; i < source.length;) {
      const start = i;
      if (source[i] === "«") {
        const end = source.indexOf("»", i + 1);
        i = end < 0 ? source.length : end + 1;
        literals.push({ start, end: i });
        // Identifier contents are opaque to command and delimiter scanning. Keep
        // non-whitespace placeholders so a preceding marker cannot cross a name.
        for (let j = start; j < i; j++) if (chars[j] !== "\n" && chars[j] !== "\r") chars[j] = "x";
      } else if (source[i] === "'" && !/[\p{L}\p{N}_']/u.test(source[i - 1] || " ")) {
        const literal = source.slice(i).match(/^'(?:\\(?:x[\da-fA-F]{2}|u[\da-fA-F]{4}|U[\da-fA-F]{8}|.)|[^'\\\r\n])'/u);
        if (literal) { i += literal[0].length; literals.push({ start, end: i }); blank(start, i); }
        else i++;
      } else if (source.startsWith("--", i)) {
        const end = source.indexOf("\n", i);
        i = end < 0 ? source.length : end;
        comments.push({ start, end: i, text: source.slice(start, i), kind: "line" });
        blank(start, i);
      } else if (source.startsWith("/-", i)) {
        let depth = 1;
        i += 2;
        while (i < source.length && depth) {
          if (source.startsWith("/-", i)) { depth++; i += 2; }
          else if (source.startsWith("-/", i)) { depth--; i += 2; }
          else i++;
        }
        comments.push({ start, end: i, text: source.slice(start + 3, depth ? i : i - 2),
          kind: source.startsWith("/--", start) ? "doc" : "block" });
        blank(start, i);
      } else if (source[i] === '"') {
        i++;
        while (i < source.length) {
          if (source[i] === "\\") i += 2;
          else if (source[i++] === '"') break;
        }
        blank(start, Math.min(i, source.length));
        literals.push({ start, end: Math.min(i, source.length) });
      } else i++;
    }
    return { masked: chars.join(""), comments, literals };
  }

  // Recognize a bundled proof whose comments or formatting predate result labels.
  // Literal contents remain exact; this key supplies navigation labels only.
  function exampleKey(source, legacyOutputNames = false) {
    const { comments, literals } = scan(source);
    const chars = source.split("");
    for (const comment of comments) for (let i = comment.start; i < comment.end; i++) chars[i] = " ";
    const code = chars.join("");
    const parts = [];
    const normalize = (text) => {
      const spaced = text.replace(/\s+/g, " ");
      return legacyOutputNames
        ? spaced.replace(/\bis_Output_([A-Za-z_][A-Za-z_0-9]*)\b/g, "$1.Returns") : spaced;
    };
    let start = 0;
    for (const literal of literals) {
      parts.push(normalize(code.slice(start, literal.start)), source.slice(literal.start, literal.end));
      start = literal.end;
    }
    parts.push(normalize(code.slice(start)));
    return parts.join("").trim();
  }

  function declarations(source) {
    const { masked, comments } = scan(source);
    const lines = [0];
    for (let i = 0; i < source.length; i++) if (source[i] === "\n") lines.push(i + 1);
    const lineAt = (offset) => {
      let low = 0, high = lines.length;
      while (low + 1 < high) {
        const mid = (low + high) >> 1;
        if (lines[mid] <= offset) low = mid; else high = mid;
      }
      return low + 1;
    };
    // Attributes may precede a declaration on the same line. Their arguments are
    // retained in the statement; only theorem/lemma commands enter this outline.
    const command = /^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*(theorem|lemma|def|abbrev|instance|example|structure|inductive|namespace|section|end|open|import|set_option|variable)\b/gm;
    const commands = [...masked.matchAll(command)];
    const entries = [];
    const occurrences = new Map();
    const scopes = [];
    const trivia = (text) => /^(?:\s|@\[[\s\S]*?\])*$/.test(text);
    let commentIndex = 0;
    let preceding = [];
    for (let index = 0; index < commands.length; index++) {
      const match = commands[index];
      if (match[1] === "namespace" || match[1] === "section") {
        const name = source.slice(match.index + match[0].length).match(/^[ \t]+((?:«[^»]+»|[^\s«])+)/)?.[1];
        scopes.push(match[1] === "namespace" ? name || "" : "");
      } else if (match[1] === "end") scopes.pop();
      if (!['theorem', 'lemma'].includes(match[1])) continue;
      const start = match.index;
      const afterKeyword = start + match[0].length;
      const nameMatch = source.slice(afterKeyword).match(/^[ \t]+((?:«[^»]+»|[^\s(:«])+)/);
      if (!nameMatch) continue;
      const name = nameMatch[1];
      while (commentIndex < comments.length && comments[commentIndex].end <= start) {
        preceding.push(comments[commentIndex++]);
      }
      preceding = preceding.filter((comment) => trivia(masked.slice(comment.end, start)));
      const marker = preceding.filter((comment) => comment.kind === "line")
        .map((comment) => comment.text.match(/^--\s*Main result:\s*(.+?)\s*$/)?.[1]).filter(Boolean).at(-1);
      const doc = preceding.filter((comment) => comment.kind === "doc").at(-1)?.text.trim() || "";
      const limit = commands[index + 1]?.index ?? source.length;
      let depth = 0, separator = -1, pendingLet = 0;
      for (let i = afterKeyword + nameMatch[0].length; i < limit; i++) {
        const char = masked[i];
        if (char === "«") { i = masked.indexOf("»", i + 1); if (i < 0) break; continue; }
        if ("([{⟨".includes(char)) depth++;
        else if (")]}⟩".includes(char)) depth--;
        if (depth === 0 && !/[\p{L}\p{N}_']/u.test(masked[i - 1] || " ")) {
          const binding = masked.slice(i).match(/^(?:letI'?|let|haveI'?|have)(?![\p{L}\p{N}_'])/u);
          if (binding) { pendingLet++; i += binding[0].length - 1; }
        }
        if (depth === 0 && masked.startsWith(":=", i)) {
          if (pendingLet) { pendingLet--; i++; }
          else { separator = i; break; }
        }
      }
      const occurrence = occurrences.get(name) || 0;
      occurrences.set(name, occurrence + 1);
      entries.push({ name, start, namespace: scopes.filter(Boolean).join("."),
        id: JSON.stringify([name, occurrence]), label: marker || null, description: doc, line: lineAt(start),
        statement: separator >= 0 ? source.slice(start, separator).trim() : null });
    }
    return entries;
  }

  // Navigation survives edits to proof bodies and surrounding helper lemmas.
  // Require a named scope and the same statement, preserving literal contents.
  // The old generated output name is an alias of the public Returns interface.
  function resultKey(entry) {
    return entry.namespace && entry.statement
      ? JSON.stringify([entry.namespace, entry.name, exampleKey(entry.statement, true)]) : null;
  }

  function create(container, { document, onJump, highlight }) {
    let previous = null;
    let selected = null;
    const examples = new Map();
    const results = new Map();
    return {
      setExamples(sources) {
        examples.clear();
        results.clear();
        for (const source of sources) {
          const entries = declarations(source);
          const main = entries.filter((entry) => entry.label);
          examples.set(exampleKey(source), new Map(main.map((entry) => [entry.id, entry.label])));
          for (const entry of entries) {
            const key = resultKey(entry);
            if (!key) continue;
            // Conflicting selections are ambiguous; do not guess a category.
            if (results.has(key) && results.get(key) !== entry.label) results.set(key, undefined);
            else if (!results.has(key)) results.set(key, entry.label);
          }
        }
        const current = previous;
        previous = null;
        if (current !== null) this.update(current);
      },
      update(source, refreshInterface = false) {
        if (source === previous && !refreshInterface) return;
        previous = source;
        const entries = declarations(source);
        const labels = examples.size ? examples.get(exampleKey(source)) : null;
        // Matching bundled proofs use the current curated selection, including
        // removals. This updates navigation for saved copies without editing them.
        if (labels) for (const entry of entries) entry.label = labels.get(entry.id) || null;
        else for (const entry of entries) {
          const key = resultKey(entry);
          if (key && results.has(key) && results.get(key) !== undefined) entry.label = results.get(key);
        }
        const main = entries.filter((entry) => entry.label);
        container.replaceChildren();
        container.hidden = false;
        const heading = document.createElement("h3");
        heading.textContent = "Main results";
        const toolbar = document.createElement("div");
        toolbar.className = "proof-outline-toolbar";
        const chooser = document.createElement("label");
        chooser.textContent = "All theorems ";
        const select = document.createElement("select");
        select.setAttribute("aria-label", "Find a theorem");
        select.disabled = entries.length === 0;
        const placeholder = document.createElement("option");
        placeholder.value = "";
        placeholder.textContent = `Choose a theorem (${entries.length})`;
        select.append(placeholder);
        entries.forEach((entry, index) => {
          const option = document.createElement("option");
          option.value = String(index);
          option.textContent = `${entry.name} · line ${entry.line}`;
          select.append(option);
        });
        chooser.append(select);
        toolbar.append(heading, chooser);
        const buttons = document.createElement("div");
        buttons.className = "proof-main-results";
        const preview = document.createElement("section");
        preview.id = "analysis-theorem-preview";
        preview.className = "proof-statement";
        preview.hidden = true;
        const resultButtons = [];
        function show(entry) {
          selected = entry.id;
          select.value = String(entries.indexOf(entry));
          preview.replaceChildren();
          preview.hidden = false;
          resultButtons.forEach(({ button, value }) => button.setAttribute("aria-pressed", String(value === entry)));
          const title = document.createElement("h4");
          title.textContent = entry.name;
          preview.append(title);
          if (entry.description) {
            const description = document.createElement("p");
            description.textContent = entry.description;
            preview.append(description);
          }
          const statement = document.createElement(entry.statement ? "pre" : "p");
          statement.textContent = entry.statement || "Open this declaration in the proof editor to read its full statement.";
          if (entry.statement && highlight) statement.innerHTML = highlight(entry.statement, entry);
          preview.append(statement);
          const jump = document.createElement("button");
          jump.type = "button";
          jump.className = "button button-quiet";
          jump.textContent = `Go to proof · line ${entry.line}`;
          jump.addEventListener("click", () => onJump(entry.line, 1));
          preview.append(jump);
        }
        const shownCategories = new Set();
        for (const entry of main) {
          const labels = entry.label === "Correctness and running time"
            ? ["Correctness", "Running time"] : [entry.label];
          for (const label of labels) {
            // One principal theorem per category keeps the overview short. All
            // declarations, including alternate implementations, remain selectable.
            if (label === "Correctness" || label === "Running time") {
              if (shownCategories.has(label)) continue;
              shownCategories.add(label);
            }
            const button = document.createElement("button");
            button.type = "button";
            button.className = "button button-quiet";
            button.textContent = label;
            button.title = entry.name;
            button.setAttribute("aria-controls", preview.id);
            button.setAttribute("aria-pressed", "false");
            button.addEventListener("click", () => show(entry));
            resultButtons.push({ button, value: entry });
            buttons.append(button);
          }
        }
        select.addEventListener("change", () => {
          if (select.value !== "" && entries[Number(select.value)]) show(entries[Number(select.value)]);
          else { selected = null; preview.hidden = true; resultButtons.forEach(({ button }) => button.setAttribute("aria-pressed", "false")); }
        });
        container.append(toolbar, buttons, preview);
        if (!main.length) {
          const hint = document.createElement("p");
          hint.className = "proof-outline-hint";
          hint.textContent = entries.length
            ? "No main results are marked in this analysis. Choose a theorem above, or add a comment like ‘-- Main result: Correctness’ before a theorem."
            : "Load an example with a Lean analysis, or write a theorem to see its statement here.";
          container.append(hint);
        }
        const current = entries.find((entry) => entry.id === selected) || main[0];
        if (current) show(current); else selected = null;
      },
    };
  }
  return { declarations, create };
});
