// The generated Lean interface: entry normalization and grouping for the panel,
// and a display lexer that colors source-facing names by their kind.
export const GROUPS = [
  { id: "outputs", title: "Outputs", categories: ["output"] },
  { id: "probability", title: "Probability", categories: ["probability"] },
  { id: "calls", title: "Calls", categories: ["execution", "helper"] },
  { id: "transcripts", title: "Transcripts", categories: ["transcript"] },
  { id: "locations", title: "Named locations and values", categories: ["location", "observation"] },
  { id: "inputs", title: "Inputs", categories: ["input"] },
  { id: "storage", title: "Heaps, objects, and clocks", categories: ["storage"] },
  { id: "advanced", title: "Advanced · local execution", categories: ["advanced"] },
];

export const KINDS = { proposition: "Proposition", theorem: "Theorem", definition: "Value", type: "Type" };
const WORDS = new Set("def abbrev theorem lemma example inductive structure class where namespace section end import open scoped if then else let in match with by fun set_option deriving private protected noncomputable mutual variable variables instance opaque axiom".split(" "));
const TYPES = new Set("Int Real ℝ Seq Tuple1 Set Bool Prop Type Sort Nat Unit String Char List Option Array Fin Prod Sum Except Heap Clocks SeqRef Configuration Transcript Stack ENNReal".split(" "));
// These imported mathematical aliases are used by bundled analyses, whose
// editor response does not include the library source. Keep them qualified.
const LIBRARY_TYPES = ["Algo2Lean.Dijkstra.Adjacency", "Algo2Lean.Dijkstra.Edges", "MeasureTheory.Measure", "Algo2LeanProbability.Run"];
const COMPONENT = "(?:«[^»\\r\\n]*»|[\\p{L}_][\\p{L}\\p{N}\\p{M}_'!?]*)";
const IDENTIFIER = new RegExp(COMPONENT + "(?:\\." + COMPONENT + ")*", "uy");
const NUMBER = /\d+/y;
const CHARACTER = /'(?:\\(?:x[\da-fA-F]{2}|u[\da-fA-F]{4}|U[\da-fA-F]{8}|.)|[^'\\\r\n])'/uy;

// These existing declarations are the small shared boundary used by analyses.
// Generated states, numbered control locations, and frame constructors are
// deliberately excluded; a proof body can still inspect their definitions.
const ADVANCED = {
  Step: ["proposition", "One permitted transition between the supplied configurations. Use it for a local transition lemma; no whole execution is required."],
  Configuration: ["type", "An execution snapshot containing the heap and either the active frame and suspended callers, or a returned result."],
  Frame: ["type", "The active invocation. Its constructors and numbered control locations are implementation details used inside proofs."],
  Result: ["type", "A returned value tagged with its source function. Prefer the ordinary result argument of Call in contracts."],
  Stack: ["type", "Suspended callers, with the most recent caller first."],
  Transcript: ["type", "A finite list of execution configurations. Validity is a separate proposition."],
};
const CORE = {
  Config: ["type", "The shared execution-configuration type, parameterized by heap, frame, and result types."],
  "Config.heap": ["definition", "Read the heap in an active or completed configuration."],
  "Config.stack": ["definition", "Read the suspended caller stack; completed configurations have an empty stack."],
  Stack: ADVANCED.Stack,
  Valid: ["proposition", "The given finite list follows the step relation from its initial configuration to its final configuration."],
  Reaches: ["proposition", "Some finite valid execution connects two configurations, without supplying a transcript as an argument."],
  Deterministic: ["proposition", "Each configuration has at most one next configuration under the supplied step relation."],
  Terminal: ["proposition", "The supplied configuration has no next step."],
  resumeConfig: ["definition", "Resume the most recent suspended caller with a result, or finish when the caller stack is empty."],
};
const STORAGE = {
  Heap: "Shared sequence, object, and collection storage together with explicit cost counters. Heap projections describe allocation, contents, and counters.",
  Seq: "Mathematical integer sequence contents: an integer value at every integer index.",
  SeqRef: "The identity of a mutable integer sequence in a heap.",
  ObjectRef: "The identity of a class instance in a heap.",
  CollectionRef: "The identity of a typed sequence, finite set, or dictionary in a heap.",
  Clocks: "Named natural-valued cost counters. Functions report increments from their caller's actual counters.",
  "Clocks.single": "A counter vector with a contribution to one named clock.",
  "Clocks.add": "Add two counter vectors pointwise.",
  "Clocks.weighted": "Sum a finite list of natural weights times the corresponding named counters.",
  clock: "Read one named counter from the supplied configuration, without a reachability hypothesis.",
  "Heap.read": "Read an integer sequence element at the supplied reference and integer index.",
  "Heap.write": "Update one integer sequence element, preserving unrelated storage.",
  "Heap.allocate": "Allocate an integer sequence with the supplied mathematical contents.",
  "Heap.cost": "The pointwise natural difference between the final and initial heap counters.",
  "Heap.tick": "Increase one named counter by a natural amount.",
  "Heap.charge": "Add a vector of clock increments to a heap.",
  "Heap.ClocksMonotone": "Every named counter is nondecreasing between the two heap snapshots.",
  "Heap.Increments": "Every final counter equals its initial value plus the supplied increment.",
  "Heap.weightedCost": "Combine the clock increments between two heaps using the supplied finite list of weights.",
  SequenceType: "A typed sequence descriptor: the element type and its storage representation.",
  "SequenceType.valid": "The reference denotes an allocated sequence with this descriptor's element type.",
  "SequenceType.get": "Read a typed element. None represents missing storage or a type mismatch.",
  "SequenceType.set": "Update a typed sequence element.",
  "SequenceType.create": "Allocate a typed sequence with the supplied mathematical contents.",
  "SequenceType.const": "Allocate a typed sequence with a constant initial value.",
  "SequenceType.copy": "Allocate a separate typed sequence with the same contents.",
  SetType: "A finite mutable set descriptor with a fixed element type and exact key equality.",
  "SetType.valid": "The reference denotes an allocated set with well-typed, distinct elements.",
  "SetType.contains": "Test membership using the descriptor's key equality.",
  "SetType.size": "Read the number of distinct elements as a natural number.",
  "SetType.keys": "Read the finite insertion-order snapshot used by iteration.",
  "SetType.create": "Allocate a set from an ordered list; repeated elements occur once.",
  "SetType.insert": "Insert an element, preserving its existing position when already present.",
  "SetType.erase": "Remove an element; an absent element leaves the set unchanged.",
  "SetType.copy": "Allocate a separate set sharing any references stored in its elements.",
  DictType: "A finite mutable dictionary descriptor with fixed key and value types.",
  "DictType.valid": "The reference denotes an allocated dictionary with well-typed entries and distinct keys.",
  "DictType.contains": "Test whether the dictionary has the supplied key.",
  "DictType.get": "Read an optional value; None represents an absent key or invalid storage.",
  "DictType.size": "Read the number of distinct keys as a natural number.",
  "DictType.keys": "Read the finite insertion-order key snapshot used by iteration.",
  "DictType.create": "Allocate a dictionary from ordered entries; later duplicate keys replace earlier values.",
  "DictType.set": "Insert or replace a value; replacement retains the key's position.",
  "DictType.erase": "Remove the supplied key without changing other entries.",
  "DictType.copy": "Allocate a separate dictionary sharing references inside its keys and values.",
};
const STORAGE_PROPS = new Set(["SequenceType.valid", "SetType.valid", "DictType.valid", "Heap.ClocksMonotone", "Heap.Increments"]);
const STORAGE_TYPES = new Set(["Heap", "Seq", "SeqRef", "ObjectRef", "CollectionRef", "Clocks", "SequenceType", "SetType", "DictType"]);
const COST_TOOLS = new Set(["Heap.ClocksMonotone", "Heap.Increments", "Heap.weightedCost", "Clocks.weighted"]);
const FINITE_STORAGE = /^(?:SetType|DictType)(?:\.|$)/;

function storageFile(name) {
  if (FINITE_STORAGE.test(name)) return "Algo2LeanLib/FiniteCollections.lean";
  return COST_TOOLS.has(name) ? "Algo2LeanLib/CallCost.lean" : "Algo2Lean.lean";
}

function extraInterface(namespace, name, command) {
  if (namespace.startsWith("Algo2LeanCore.")) { name = namespace.slice(14) + "." + name; namespace = "Algo2LeanCore"; }
  if (/^Algo2LeanGenerated\.(?:SequenceType|SetType|DictType)$/.test(namespace)) {
    name = namespace.slice("Algo2LeanGenerated.".length) + "." + name;
    namespace = "Algo2LeanGenerated";
  }
  if (namespace === "Algo2LeanCore" && CORE[name]) return { category: "advanced", kind: CORE[name][0], meaning: CORE[name][1] };
  if (!/(?:^|\.)Algo2LeanGenerated$/.test(namespace)) return null;
  if (ADVANCED[name]) return { category: "advanced", kind: ADVANCED[name][0], meaning: ADVANCED[name][1] };
  if (namespace === "Algo2LeanGenerated" && STORAGE[name]) return { category: "storage",
    kind: STORAGE_PROPS.has(name) ? "proposition" : STORAGE_TYPES.has(name) ? "type" : "definition", meaning: STORAGE[name] };
  const prefix = name.match(/^(Ref|is|field|set|create|seq)_/);
  if (!prefix || name.includes("_a2l_import_")) return null;
  const meaning = {
    Ref: "Reference type for the named source class. The referenced object's fields live in the supplied heap.",
    is: "Shallow class membership: this reference is allocated with the named class tag. This does not assert recursive validity of its fields.",
    field: "Read a named source field with its declared type. None means the field is missing or has the wrong stored type.",
    set: "Write a named source field with its declared type.",
    create: "Build input data directly in a heap. This helper does not execute the source constructor.",
    seq: "The typed sequence descriptor for this source element type. Use its valid, get, set, create, const, and copy operations.",
  };
  const theorem = ["theorem", "lemma"].includes(command);
  return { category: "storage", kind: theorem ? "theorem" : prefix[1] === "is" ? "proposition" : prefix[1] === "Ref" ? "type" : "definition",
    meaning: theorem ? "Reading the named field after its typed update returns the supplied value, under the stated validity hypothesis." : meaning[prefix[1]] };
}

// This is a display lexer, not a Lean elaborator. Each token retains its exact
// text and offsets so the highlighted and selectable layers have identical geometry.
export function tokenize(source) {
  const tokens = [];
  for (let i = 0; i < source.length;) {
    const start = i;
    let kind = "plain";
    if (source.startsWith("--", i)) {
      const end = source.indexOf("\n", i);
      i = end < 0 ? source.length : end;
      kind = "comment";
    } else if (source.startsWith("/-", i)) {
      let depth = 1;
      i += 2;
      while (i < source.length && depth) {
        if (source.startsWith("/-", i)) { depth++; i += 2; }
        else if (source.startsWith("-/", i)) { depth--; i += 2; }
        else i++;
      }
      kind = "comment";
    } else if (source[i] === '"') {
      i++;
      while (i < source.length) {
        if (source[i] === "\\") i = Math.min(i + 2, source.length);
        else if (source[i++] === '"') break;
      }
      kind = "string";
    } else {
      CHARACTER.lastIndex = IDENTIFIER.lastIndex = NUMBER.lastIndex = i;
      const character = source[i] === "'" && CHARACTER.exec(source);
      const identifier = !character && IDENTIFIER.exec(source);
      const number = !character && !identifier && NUMBER.exec(source);
      if (character) { i += character[0].length; kind = "string"; }
      else if (identifier) { i += identifier[0].length; kind = WORDS.has(identifier[0]) ? "keyword" : "identifier"; }
      else if (number) { i += number[0].length; kind = "number"; }
      else if (source[i] === "«") { i = source.length; kind = "identifier"; }
      else i++;
    }
    const text = source.slice(start, i);
    const previous = tokens[tokens.length - 1];
    if (kind === "plain" && previous?.kind === "plain") { previous.end = i; previous.text += text; }
    else tokens.push({ start, end: i, text, kind });
  }
  return tokens;
}

export function classify(entry) {
  if (Object.hasOwn(KINDS, entry.kind)) return entry.kind;
  if (entry.category === "observation") return "definition";
  if (entry.category === "location") return "proposition";
  if (entry.category === "helper" || /\.(?:Returns\.withCost|ReturnsWithCost\.returns|ParallelCall\.call|Call\.(?:run|hasLaw|expectedReturn)|Run\.eq_of_call|returnProbability_eq_expectedReturn)$/.test(entry.name)) return "theorem";
  if (["output", "execution", "transcript"].includes(entry.category) || /\.(?:ValidInput|HasLaw)$/.test(entry.name)) return "proposition";
  return "definition";
}

function memberKind(name) {
  // Observation names can themselves be Call or Returns; inspect them first.
  const parts = name.match(new RegExp(COMPONENT, "gu")) || [];
  if (["Local", "Element"].includes(parts[parts.length - 2])) return "definition";
  if (parts[parts.length - 2] === "At") return "proposition";
  if (/\.(?:Returns\.withCost|ReturnsWithCost\.returns|ParallelCall\.call|Call\.(?:run|hasLaw|expectedReturn)|Run\.eq_of_call|returnProbability_eq_expectedReturn)$/.test(name)) return "theorem";
  if (/\.(?:Returns|ReturnsWithCost|Call|ParallelCall|Run|CallFrom|ValidTranscript|ValidHeapTranscript|ValidInput|HasLaw)$/.test(name)) return "proposition";
  if (/\.(?:initial|load|outcome|law|returnProbability|outputProbability|terminationProbability|cost|expectedCost|costProbability|expectedReturn|expectedFrom)$/.test(name)) return "definition";
  return null;
}

function qualify(namespace, name) {
  return name.startsWith("_root_.") ? name.slice(7) : [namespace, name].filter(Boolean).join(".");
}

function canonical(name) {
  return (name.match(new RegExp(COMPONENT, "gu")) || []).map((part) =>
    /^«[\p{L}_][\p{L}\p{N}\p{M}_'!?]*»$/u.test(part) ? part.slice(1, -1) : part).join(".");
}

// Track ordinary namespace/open commands. We intentionally do not guess Lean's
// type-directed field notation: `proof.returns` needs elaboration to resolve.
function walk(source, tokens, visit) {
  let namespace = "";
  let opened = [];
  let scopeId = 0;
  const scopes = [];
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    const prefix = source.slice(source.lastIndexOf("\n", token.start - 1) + 1, token.start);
    const command = token.kind === "keyword" && /^[ \t]*(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*$/.test(prefix);
    const next = tokens.slice(i + 1, i + 4).find((item) => item.kind !== "plain" && item.kind !== "comment");
    if (command && ["namespace", "section"].includes(token.text)) {
      scopeId++;
      scopes.push({ namespace, opened });
      opened = [...opened];
      if (token.text === "namespace" && next?.kind === "identifier") namespace = qualify(namespace, next.text);
    } else if (command && token.text === "end") {
      scopeId++;
      const scope = scopes.pop();
      if (scope) { namespace = scope.namespace; opened = scope.opened; }
    } else if (command && token.text === "open") {
      scopeId++;
      for (let j = i + 1; j < tokens.length && !tokens[j].text.includes("\n"); j++) {
        if (tokens[j].kind === "identifier") {
          opened.push(tokens[j].text);
          if (namespace) opened.push(qualify(namespace, tokens[j].text));
        }
        else if (tokens[j].kind !== "plain") break;
        if (tokens[j].text.includes("(")) break;
      }
    }
    visit(token, { namespace, opened, scopeId, command, next, index: i });
  }
}

function simpleTypeAlias(tokens, start, offset, types, context) {
  let depth = 0;
  let needsType = true;
  let seen = false;
  for (let i = start; i < tokens.length; i++) {
    const token = tokens[i];
    if (token.kind === "comment") continue;
    if (token.kind === "plain") {
      const text = i === start ? token.text.slice(offset) : token.text;
      for (const char of text) {
        if (char === "\n" && !depth && seen) return !needsType;
        // Equality, logical connectives, and other term operators cannot
        // establish a type alias. Leave complex expressions to Lean itself.
        if (!/[\s()[\]{},×→]/u.test(char)) return false;
        if ("([{⦃".includes(char)) depth++;
        else if (")]}⦄".includes(char)) depth--;
        else if (char === "→" || char === "×") needsType = true;
      }
    } else if (token.kind === "identifier") {
      if (needsType && !resolve(token.text, types, context)) return false;
      needsType = false;
      seen = true;
    } else if (token.kind !== "number" || needsType) return false;
  }
  return seen && !needsType && depth === 0;
}

// Detect declared data types and simple type aliases without elaborating Lean.
// Only inspect declaration headers and alias heads, never proof bodies. In
// particular, a capitalized name or a declaration returning Prop is not enough.
function collectTypes(source, tokens, types) {
  walk(source, tokens, (token, context) => {
    if (!context.command || !["structure", "class", "inductive", "abbrev", "def"].includes(token.text)
        || context.next?.kind !== "identifier") return;
    const data = ["structure", "class", "inductive"].includes(token.text);
    let depth = 0;
    let annotation = null;
    let result = "";
    let rhsOffset = null;
    let end = context.index + 1;
    header: for (; end < tokens.length; end++) {
      const part = tokens[end];
      if (part.start < context.next.end || part.kind === "comment") continue;
      if (!depth && part.kind === "keyword") break;
      if (part.kind === "plain") {
        for (let i = 0; i < part.text.length; i++) {
          const char = part.text[i];
          if (!depth && part.text.startsWith(":=", i)) { rhsOffset = i + 2; break header; }
          if (!depth && char === "|") break header;
          if (!depth && char === ":") { annotation = true; continue; }
          if (annotation) result += char;
          if ("([{⦃".includes(char)) depth++;
          else if (")]}⦄".includes(char)) depth--;
        }
      } else if (annotation) result += part.text;
    }
    let isType = annotation ? /^(?:Type|Sort)\b/.test(result.split("→").pop().trim()) : data;
    if (!data && !annotation && rhsOffset !== null) isType = simpleTypeAlias(tokens, end, rhsOffset, types, context);
    if (isType) types.set(canonical(qualify(context.namespace, context.next.text)), "type");
  });
  return types;
}

function typeCatalog(catalog) {
  const types = new Map([...TYPES, ...LIBRARY_TYPES].map((name) => [name, "type"]));
  for (const [name, kind] of catalog.types || []) types.set(name, kind);
  for (const [name, kind] of catalog) if (kind === "type") types.set(name, kind);
  return types;
}

export function createCatalog(functions = [], sources = []) {
  const names = new Map();
  const extraEntries = new Map();
  const finiteCollections = sources.some((source) => typeof source === "string" &&
    /\bAlgo2LeanLib\.FiniteCollections\b|\bstructure\s+(?:SetType|DictType)\b/.test(source));
  // Project responses contain generated modules but may omit shared-library
  // text. Keep the documented shared boundary available in that case too.
  if (sources.some((source) => typeof source === "string" && source.length)) {
    for (const [name, [kind, meaning]] of Object.entries(CORE)) {
      const fullName = "Algo2LeanCore." + name;
      names.set(fullName, kind);
      extraEntries.set(fullName, { name: fullName, kind, meaning, category: "advanced", arguments: [], fileLabel: "Algo2Lean.lean" });
    }
    for (const [name, meaning] of Object.entries(STORAGE)) {
      if (FINITE_STORAGE.test(name) && !finiteCollections) continue;
      const fullName = "Algo2LeanGenerated." + name;
      const kind = STORAGE_PROPS.has(name) ? "proposition" : STORAGE_TYPES.has(name) ? "type" : "definition";
      names.set(fullName, kind);
      extraEntries.set(fullName, { name: fullName, kind, meaning, category: "storage", arguments: [], fileLabel: storageFile(name) });
    }
  }
  for (const source of sources) {
    if (typeof source !== "string") continue;
    walk(source, tokenize(source), (token, context) => {
      if (!context.command || !["def", "abbrev", "theorem", "lemma", "inductive", "structure", "class"].includes(token.text) || context.next?.kind !== "identifier") return;
      const name = qualify(context.namespace, context.next.text);
      const extra = extraInterface(context.namespace, context.next.text, token.text);
      const kind = extra?.kind || memberKind(context.next.text);
      if (kind) names.set(canonical(name), kind);
      if (extra) extraEntries.set(name, { ...extra, name, namespace: context.namespace, arguments: [],
        signature: declarationHeader(source.slice(token.start)), file_kind: "core",
        fileLabel: /^Algo2LeanGenerated\.(?:SetType|DictType)$/.test(context.namespace) ||
          (context.namespace === "Algo2LeanGenerated" && FINITE_STORAGE.test(context.next.text))
            ? "Algo2LeanLib/FiniteCollections.lean"
            : context.namespace.startsWith("Algo2LeanCore") || context.namespace === "Algo2LeanGenerated.SequenceType" ||
              (context.namespace === "Algo2LeanGenerated" && STORAGE[context.next.text]) ? "Algo2Lean.lean" : "Algorithm definitions" });
    });
  }
  for (const entry of normalizeEntries(functions)) names.set(canonical(entry.name), classify(entry));
  names.extraEntries = [...extraEntries.values()];
  names.types = typeCatalog(names);
  for (const source of sources) if (typeof source === "string") collectTypes(source, tokenize(source), names.types);
  return names;
}

export function declarationHeader(source) {
  let depth = 0;
  for (const token of tokenize(source.slice(0, 8192))) {
    if (!depth && token.kind === "keyword" && token.text === "where") return source.slice(0, token.start).trim();
    if (token.kind !== "plain") continue;
    for (let i = token.start; i < token.end; i++) {
      if (!depth && source.startsWith(":=", i)) {
        const header = source.slice(0, i).trim();
        // An alias has no explicit type; retain its target in the specification.
        if (/^abbrev [^\s:]+$/.test(header)) return source.slice(0, source.indexOf("\n", i) < 0 ? source.length : source.indexOf("\n", i)).trim();
        return header;
      }
      if (!depth && source[i] === "|") return source.slice(0, i).trim();
      if ("([{⦃".includes(source[i])) depth++;
      else if (")]}⦄".includes(source[i])) depth--;
    }
  }
  return source.split("\n")[0];
}

function resolve(name, catalog, { namespace, opened }) {
  name = canonical(name);
  namespace = canonical(namespace);
  opened = opened.map(canonical);
  if (name.startsWith("_root_.")) return catalog.get(name.slice(7));
  const parts = namespace.match(new RegExp(COMPONENT, "gu")) || [];
  for (; parts.length; parts.pop()) {
    const scope = parts.join(".");
    if (catalog.has(scope + "." + name)) return catalog.get(scope + "." + name);
  }
  if (catalog.has(name)) return catalog.get(name);
  const kinds = new Set(opened.map((scope) => catalog.get(scope + "." + name)).filter(Boolean));
  return kinds.size === 1 ? [...kinds][0] : null;
}

// Display tokens for Lean text: {text, className, title}. The concatenated
// texts equal the source exactly. A prefix supplies namespace and open context
// without being displayed.
export function highlightTokens(source, catalog = new Map(), prefix = "") {
  const output = [];
  const scopes = new Map();
  const fullSource = prefix + source;
  const tokens = tokenize(fullSource);
  const types = collectTypes(fullSource, tokens, typeCatalog(catalog));
  walk(fullSource, tokens, (token, context) => {
    if (token.end <= prefix.length) return;
    let role = null;
    if (token.kind === "identifier") {
      if (!scopes.has(context.scopeId)) scopes.set(context.scopeId, new Map());
      const cache = scopes.get(context.scopeId);
      if (!cache.has(token.text)) cache.set(token.text, resolve(token.text, catalog, context)
        || (resolve(token.text, types, context) ? "syntax-type" : null));
      role = cache.get(token.text);
    }
    const syntax = ["comment", "string", "number", "keyword"].includes(token.kind) ? token.kind
      : TYPES.has(token.text) ? "type" : null;
    const className = role === "syntax-type" ? "token-type" : role ? "interface-" + role : syntax ? "token-" + syntax : null;
    const title = role && role !== "syntax-type" ? KINDS[role] : null;
    const text = token.text.slice(Math.max(0, prefix.length - token.start));
    output.push({ text, className, title });
  });
  return output;
}

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

export function normalizeEntries(functions) {
  const entries = [];
  const seen = new Set();
  for (const fn of Array.isArray(functions) ? functions : []) {
    if (!fn || typeof fn !== "object") continue;
    const raw = Array.isArray(fn.interface_entries) ? fn.interface_entries : summaryEntries(fn);
    for (const entry of raw) {
      if (!entry || typeof entry.name !== "string" || !entry.name) continue;
      if (/(?:^|\.)(?:is_(?:OutputWithCost|Output|Execution|SummaryFrom|Summary|HeapTranscript|Transcript)_|At_|local_|element_|validInputs_|initial_|load_)[^.]+(?:\.(?:output|withCost|execution|eq_of_summary))?$/.test(entry.name)) continue;
      const fileKind = ["core", "points", "facts", "probability", "parallel"].includes(entry.file_kind) ? entry.file_kind : "core";
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

export function groupEntries(entries) {
  return GROUPS.map((group) => ({ id: group.id, title: group.title,
    entries: entries.filter((entry) => group.categories.includes(entry.category)) }))
    .filter((group) => group.entries.length);
}

// Entries shown by the interface panel: compiler metadata plus the curated
// shared boundary discovered in the generated sources.
export function panelEntries(functions, catalog) {
  const functionEntries = normalizeEntries(functions);
  const entries = [...functionEntries, ...(catalog?.extraEntries || [])];
  const missing = !functionEntries.length && Array.isArray(functions) && functions.some((fn) => fn && typeof fn.name === "string");
  return { entries, missing };
}
