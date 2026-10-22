// Publication details never inspect source, proofs, or drafts.
export function externalUrl(address) {
  if (typeof address !== "string") return null;
  try {
    const url = new URL(address);
    if (url.protocol === "https:" && !url.username && !url.password) return url.href;
  } catch (_) { /* Malformed publication URLs stay hidden. */ }
  return null;
}

export function peopleEntries(people) {
  if (!Array.isArray(people)) return [];
  return people.map((person) => ({
    name: [person?.given_names, person?.family_names].filter(Boolean).join(" "),
    website: externalUrl(person?.website),
  })).filter((person) => person.name);
}

export function validPublication(data) {
  return Boolean(data) && typeof data.version === "string" && Array.isArray(data.authors);
}

export function versionLabel(data) {
  return data.status === "development" ? `${data.version} · Development build` : data.version;
}
