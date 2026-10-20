// Literal, case-insensitive search over editor text. Offsets index the original string.
export function matches(text, query) {
  if (!query) return [];
  const expression = new RegExp(query.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"), "giu");
  return [...text.matchAll(expression)].map((match) => ({ start: match.index, end: match.index + match[0].length }));
}
