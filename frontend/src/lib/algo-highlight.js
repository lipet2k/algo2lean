// Display tokens for the Python-like source. Every character of the input is
// retained so the highlight layer and the textarea keep identical geometry.
const WORDS = new Set(["class", "def", "import", "from", "as", "if", "else", "elif", "while", "for", "in", "return", "pass",
  "and", "or", "not", "is", "None", "True", "False", "break", "continue", "del"]);
const BUILTINS = new Set(["const", "copy", "update", "range", "tick", "randint", "fork_join", "len", "set"]);
const TYPES = new Set(["Int", "Real", "Seq", "Tuple", "Set", "Dict", "Bool", "Prop", "Nat", "Unit", "True", "False"]);
const PATTERN = /#[^\n]*|"(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|(?:\b\d(?:_?\d)*(?:\.(?:\d(?:_?\d)*)?)?|\.\d(?:_?\d)*)(?:[eE][+-]?\d(?:_?\d)*)?|\b[A-Za-z_][A-Za-z_0-9]*\b/g;

export function algoTokens(value) {
  const tokens = [];
  let cursor = 0;
  const plain = (text) => { if (text) tokens.push({ text, className: null }); };
  for (const match of value.matchAll(PATTERN)) {
    plain(value.slice(cursor, match.index));
    const token = match[0];
    let kind = "";
    if (token.startsWith("#")) kind = "comment";
    else if (token.startsWith('"') || token.startsWith("'")) kind = "string";
    else if (/^[\d.]/.test(token)) kind = "number";
    else if (WORDS.has(token)) kind = "keyword";
    else if (TYPES.has(token)) kind = "type";
    else if (BUILTINS.has(token) || /^\s*\(/.test(value.slice(match.index + token.length))) kind = "function";
    tokens.push({ text: token, className: kind ? `token-${kind}` : null });
    cursor = match.index + token.length;
  }
  plain(value.slice(cursor));
  return tokens;
}
