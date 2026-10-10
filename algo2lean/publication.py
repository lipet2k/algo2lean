"""One source of publication metadata, citations, and generated-file credit.

No release is implied by a development version. Software citation authors,
creators, and contributors are explicit, separate roles in the metadata;
public destinations remain unset until configured by the owners.
Metadata does not contain user source, line labels, timestamps, or local checkout identities.
"""

import argparse
import json
from pathlib import Path
import re
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parent.parent


class PublicationError(ValueError):
    """The compiler's versioned publication resource needs repair."""


def _text(value, field):
    if not isinstance(value, str) or not value.strip() or any(ord(c) < 32 for c in value):
        raise ValueError("Publication %s must be nonempty, single-line text." % field)
    return value


def compiler_metadata(root=None):
    """Validate only the identity used in generated credit, independently of citations."""
    path = (Path(root) if root is not None else ROOT) / "publication.json"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise PublicationError("Cannot read the compiler's publication.json. Restore its versioned metadata file.") from error
    try:
        if not isinstance(data, dict):
            raise ValueError("Publication metadata must be a JSON object.")
        for field in ("title", "version"):
            _text(data.get(field), field)
        if not re.fullmatch(r"[A-Za-z0-9.+-]+", data["version"]):
            raise ValueError("Publication version must contain only letters, digits, dots, pluses, or hyphens.")
        repository = data.get("repository_url")
        if repository is not None:
            _text(repository, "repository_url")
            url = urlsplit(repository)
            if url.scheme != "https" or not url.netloc or url.username or url.password:
                raise ValueError("Publication repository_url must be a public HTTPS URL.")
    except ValueError as error:
        raise PublicationError("Invalid compiler metadata in publication.json: %s" % error) from error
    return data


def metadata(root=None):
    """Read and validate the full citation metadata without Git or clock lookups."""
    data = compiler_metadata(root)
    _text(data.get("status"), "status")
    if data["status"] not in {"development", "release"}:
        raise ValueError("Publication status must be development or release.")
    # Creator and contributor credit is never inferred from citation authorship.
    data.setdefault("creators", [])
    data.setdefault("contributors", [])
    for role in ("authors", "creators", "contributors"):
        if not isinstance(data.get(role), list):
            raise ValueError("Publication %s must be a list." % role)
        for person in data[role]:
            if not isinstance(person, dict):
                raise ValueError("Each publication person must provide given_names and family_names.")
            for field in ("given_names", "family_names"):
                _text(person.get(field), role + " " + field)
            orcid = person.get("orcid")
            if orcid is not None and (not isinstance(orcid, str) or
                    not re.fullmatch(r"https://orcid\.org/\d{4}-\d{4}-\d{4}-\d{3}[\dX]", orcid)):
                raise ValueError("Publication ORCID must be a full https://orcid.org identifier.")
    if data.get("doi") is not None:
        _text(data["doi"], "doi")
        if not re.fullmatch(r"10\.\d{4,9}/\S+", data["doi"]):
            raise ValueError("Publication DOI must be an identifier beginning 10., without a URL prefix.")
    return data


def citation_text(data):
    """A readable software citation, or None until authorship is configured."""
    if not data["authors"]:
        return None
    authors = "; ".join(author["given_names"] + " " + author["family_names"] for author in data["authors"])
    kind = "Computer software; development version" if data["status"] == "development" else "Computer software"
    citation = "%s. %s (version %s) [%s]." % (authors, data["title"], data["version"], kind)
    destination = "https://doi.org/" + data["doi"] if data.get("doi") else data.get("repository_url")
    return citation + (" " + destination if destination else "")


def _bibtex(value):
    escapes = {"\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "&": r"\&",
               "%": r"\%", "_": r"\_", "#": r"\#", "$": r"\$", "~": r"\textasciitilde{}",
               "^": r"\textasciicircum{}"}
    return "".join(escapes.get(character, character) for character in value)


def bibtex(data):
    if not data["authors"]:
        return None
    authors = " and ".join(_bibtex(author["family_names"]) + ", " + _bibtex(author["given_names"])
                           for author in data["authors"])
    fields = [("author", authors), ("title", _bibtex(data["title"])), ("version", _bibtex(data["version"]))]
    if data["status"] == "development":
        fields.append(("note", "Development version; unreleased"))
    if data.get("repository_url"):
        fields.append(("url", _bibtex(data["repository_url"])))
    if data.get("doi"):
        fields.append(("doi", _bibtex(data["doi"])))
    return "@software{algo2lean,\n" + "\n".join("  %s = {%s}," % item for item in fields) + "\n}\n"


def citation_cff(data):
    """Generate CFF using JSON-quoted scalars, which are valid YAML strings."""
    if not data["authors"]:
        return None
    quote = lambda value: json.dumps(value, ensure_ascii=False)
    lines = ['cff-version: 1.2.0', 'message: "If you use Algo2Lean in your research, please cite this software."',
             'type: software', 'title: ' + quote(data["title"]), 'version: ' + quote(data["version"]), 'authors:']
    for author in data["authors"]:
        lines += ['  - family-names: ' + quote(author["family_names"]),
                  '    given-names: ' + quote(author["given_names"])]
        if author.get("orcid"):
            lines.append('    orcid: ' + quote(author["orcid"]))
    if data.get("license"):
        lines.append('license: ' + quote(data["license"]))
    if data.get("repository_url"):
        lines.append('repository-code: ' + quote(data["repository_url"]))
    if data.get("doi"):
        lines.append('doi: ' + quote(data["doi"]))
    if data["status"] == "development":
        lines.append('abstract: "Development version; no numbered public release has been published yet."')
    return "\n".join(lines) + "\n"


def publication_info(root=None):
    data = metadata(root)
    return {**data, "citation": citation_text(data), "bibtex": bibtex(data),
            "citation_url": "/CITATION.cff" if data["authors"] else None}


def generated_credit():
    data = compiler_metadata()
    destination = " " + data["repository_url"] if data.get("repository_url") else ""
    return "-- Generated by %s %s%s\n" % (data["title"], data["version"], destination)


def credit_generated(source):
    """Keep imports first for existing Lean tooling and insert one stable credit."""
    lines = source.splitlines(keepends=True)
    index = 0
    while index < len(lines) and lines[index].startswith("import "):
        index += 1
    lines.insert(index, generated_credit())
    return "".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Generate or check CITATION.cff from publication.json.")
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--write-citation", action="store_true")
    actions.add_argument("--check-citation", action="store_true")
    args = parser.parse_args()
    try:
        content = citation_cff(metadata())
    except ValueError as error:
        parser.error(str(error))
    if content is None:
        parser.error("Configure authors in publication.json before creating a citation.")
    path = ROOT / "CITATION.cff"
    if args.write_citation:
        path.write_text(content, encoding="utf-8")
    elif not path.is_file() or path.read_text(encoding="utf-8") != content:
        parser.error("CITATION.cff differs from publication.json; run with --write-citation.")


if __name__ == "__main__":
    main()
