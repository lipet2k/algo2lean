import { memo, useMemo } from "react";

// Highlighted text is rendered line by line so an edit re-renders only the
// lines whose tokens changed. The concatenated text equals the input exactly.
function splitLines(tokens) {
  const lines = [[]];
  for (const token of tokens) {
    const parts = token.text.split("\n");
    parts.forEach((part, index) => {
      if (index) lines.push([]);
      if (part) lines[lines.length - 1].push(part === token.text ? token : { ...token, text: part });
    });
  }
  return lines.map((line) => ({
    tokens: line,
    signature: line.map((token) => `${token.className || ""}\u0001${token.title || ""}\u0001${token.text}`).join("\u0002"),
  }));
}

const Line = memo(function Line({ tokens, last }) {
  return (
    <>
      {tokens.map((token, index) => (token.className
        ? <span key={index} className={token.className} title={token.title || undefined}>{token.text}</span>
        : token.text))}
      {last ? null : "\n"}
    </>
  );
}, (previous, next) => previous.signature === next.signature && previous.last === next.last);

export function Tokens({ tokens }) {
  const lines = useMemo(() => splitLines(tokens), [tokens]);
  return lines.map((line, index) => (
    <Line key={index} tokens={line.tokens} signature={line.signature} last={index === lines.length - 1} />
  ));
}
