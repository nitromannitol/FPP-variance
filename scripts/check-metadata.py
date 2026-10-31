#!/usr/bin/env python3
"""Check the repository metadata and documentation (standard library only).

Usage: python3 scripts/check-metadata.py [--root DIR]

Checks, each reported as an error:

  * `lean-toolchain` names Lean 4.35.0 or later; `lake-manifest.json` has only
    git packages with 40-digit revisions, and each `require ... @ "rev"` of
    `lakefile.lean` agrees with it;
  * `CITATION.cff` has the required keys, and its authors, license and
    repository agree with `formalization.yaml`;
  * `formalization.yaml` is version v0.4 with the sections the schema requires
    (project, sources, automation, review) and the schema's enumerated values;
    its status counts no `sorry` and lists only the standard axioms; every main
    result names an existing file that declares the theorem, with only the
    standard axioms, and an existing comparator configuration; every main
    result is printed by `scripts/Axioms.lean`;
  * neither `CITATION.cff` nor `formalization.yaml` contains a `TODO`;
  * `LICENSE` is the Apache License 2.0; the two papers in `papers/` are PDFs;
    `docs/FORMALIZATION-NOTES.md` exists;
  * both workflows exist with their names and a `workflow_dispatch` trigger; one
    job with `timeout-minutes: 360`, no step above 310 minutes, no constant
    `cancel-in-progress: true`; every `uses:` pinned by a full commit hash; the
    disk-space step right after checkout (at least 20 GiB free; 30 GiB for the
    comparators) and a swap step; the build workflow's per-attempt cache key,
    saved with `if: always()`; the comparators workflow restoring the build's
    cache with `fail-on-cache-miss`, saving none, building nothing, with
    bubblewrap and the AppArmor sysctl before the comparator, and one matrix
    entry for each configuration `Audit/<Name>/comparator.json`;
  * README.md: both workflow badges, every relative link resolves, and every
    `lean` block that states a theorem is a verbatim, complete (it ends where the
    proof `:=` begins) piece of the source file declaring it;
  * README.md and the documents under `docs/` avoid the constructs that GitHub's
    math rendering breaks on: `\\operatorname`, `\\DeclareMathOperator`,
    `\\newcommand` and `\\def`, and `<` or `>` directly followed by a letter or a
    backslash inside math.

YAML is read with a small built-in reader for the subset these files use, so the
check needs no packages.

Exit status: 0 PASS, 1 FAIL.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True  # this script loads check-lean-sources.py; leave no __pycache__

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPOSITORY = "https://github.com/nitromannitol/FPP-variance"
PAPERS = ("papers/CurvatureVariance.pdf", "papers/IsotropicVariance.pdf")
HEX40 = re.compile(r"^[0-9a-f]{40}$")
# Enumerated values of the formalization.yaml v0.4 schema.
ENUMS = {
    "method": ["manual", "copilot", "agent", "autonomous", "other"],
    "relationship": ["", "formalizes", "adapts", "independently-proves", "background", "other"],
    "author_endorsement": ["", "participated", "endorsed", "no-response", "not-contacted", "declined", "n/a", "other"],
    "related": ["", "builds-on", "adapts", "independent", "supersedes", "other"],
}


# --------------------------------------------------------------------------- YAML subset

class YamlError(Exception):
    pass


KEY = re.compile(r"""^(?P<key>"(?:[^"\\]|\\.)*"|'[^']*'|[^\s:#'"\-\[\{][^:#]*?|-[^\s:][^:#]*?)\s*:(?:\s+(?P<rest>.*))?$""")


def _strip_comment(text: str) -> str:
    quote = None
    for index, char in enumerate(text):
        if quote:
            if char == quote and text[index - 1] != "\\":
                quote = None
        elif char in "\"'":
            quote = char
        elif char == "#" and (index == 0 or text[index - 1].isspace()):
            return text[:index].rstrip()
    return text.rstrip()


def _split_flow(text: str) -> list[str]:
    parts, depth, quote, current = [], 0, None, ""
    for char in text:
        if quote:
            current += char
            if char == quote:
                quote = None
        elif char in "\"'":
            quote = char
            current += char
        elif char in "[{":
            depth += 1
            current += char
        elif char in "]}":
            depth -= 1
            current += char
        elif char == "," and depth == 0:
            parts.append(current)
            current = ""
        else:
            current += char
    if current.strip():
        parts.append(current)
    return parts


def _scalar(text: str):
    text = _strip_comment(text).strip()
    if text.startswith('"'):
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            return text[1:-1]
    if text.startswith("'") and text.endswith("'") and len(text) >= 2:
        return text[1:-1].replace("''", "'")
    if text.startswith("["):
        return [_scalar(part) for part in _split_flow(text[1:text.rindex("]")])]
    if text.startswith("{"):
        return {}
    if text in ("true", "True"):
        return True
    if text in ("false", "False"):
        return False
    if text in ("null", "~", ""):
        return None
    if re.fullmatch(r"-?\d+", text):
        return int(text)
    return text


def parse_yaml(text: str):
    """Parse block mappings, block lists, quoted and plain scalars, flow lists and `>`/`|` scalars."""
    raw = [(len(line) - len(line.lstrip(" ")), line.strip(), number)
           for number, line in enumerate(text.splitlines(), 1)]
    lines = [list(item) for item in raw]
    position = 0

    def significant(start: int) -> int:
        while start < len(lines) and (not lines[start][1] or lines[start][1].startswith("#")):
            start += 1
        return start

    def block_scalar(start: int, parent_indent: int, style: str) -> tuple[str, int]:
        chunks, index = [], start
        while index < len(lines) and (not lines[index][1] or lines[index][0] > parent_indent):
            chunks.append(lines[index][1])
            index += 1
        while chunks and not chunks[-1]:
            chunks.pop()
        return ("\n" if style.startswith("|") else " ").join(chunks), index

    def parse_node(start: int, indent: int):
        start = significant(start)
        if lines[start][1] == "-" or lines[start][1].startswith("- "):
            return parse_list(start, indent)
        return parse_mapping(start, indent)

    def parse_value(rest: str | None, start: int, indent: int):
        if rest is not None and rest.startswith((">", "|")):
            return block_scalar(start, indent, rest.strip())
        if rest is not None and _strip_comment(rest):
            return _scalar(rest), start
        following = significant(start)
        if following < len(lines):
            next_indent, content = lines[following][0], lines[following][1]
            if next_indent > indent or (next_indent == indent and (content == "-" or content.startswith("- "))):
                return parse_node(following, next_indent)
        return None, start

    def parse_mapping(start: int, indent: int):
        result: dict = {}
        index = significant(start)
        while index < len(lines) and lines[index][0] == indent and not lines[index][1].startswith("- "):
            match = KEY.match(_strip_comment(lines[index][1])) if lines[index][1][0] not in "\"'" else KEY.match(lines[index][1])
            if not match:
                raise YamlError(f"line {lines[index][2]}: cannot read `{lines[index][1]}`")
            key = _scalar(match["key"]) if match["key"][0] in "\"'" else match["key"]
            value, index = parse_value(match["rest"], index + 1, indent)
            result[key] = value
            index = significant(index)
        return result, index

    def parse_list(start: int, indent: int):
        result: list = []
        index = significant(start)
        while index < len(lines) and lines[index][0] == indent and (lines[index][1] == "-" or lines[index][1].startswith("- ")):
            content = lines[index][1][1:].lstrip()
            offset = len(lines[index][1]) - len(content)
            if not _strip_comment(content):
                value, index = parse_value(None, index + 1, indent)
            elif KEY.match(_strip_comment(content)) and not content.startswith(('"', "'", "[")) or (
                    content[0] in "\"'" and KEY.match(content)):
                lines[index] = [indent + offset, content, lines[index][2]]
                value, index = parse_mapping(index, indent + offset)
            else:
                value, index = _scalar(content), index + 1
            result.append(value)
            index = significant(index)
        return result, index

    start = significant(0)
    if start >= len(lines):
        return None
    value, _ = parse_node(start, lines[start][0])
    return value


# --------------------------------------------------------------------------- checks

def load_sources_module(root: Path):
    path = root / "scripts" / "check-lean-sources.py"
    spec = importlib.util.spec_from_file_location("check_lean_sources", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_lean_sources"] = module
    spec.loader.exec_module(module)
    return module


MATH_MACROS = re.compile(r"\\(?:operatorname|DeclareMathOperator|newcommand|renewcommand|def)(?![A-Za-z])")
MATH_SPAN = re.compile(r"```math\n.*?```|\$`.*?`\$|\$\$.*?\$\$|(?<![\\$])\$(?!\$)(?:\\.|[^$\\\n])+\$", re.S)
MATH_TAG = re.compile(r"[<>][A-Za-z\\]")


class Metadata:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.errors: list[str] = []
        self.sources = load_sources_module(root)

    def error(self, message: str) -> None:
        self.errors.append(message)

    def text(self, name: str) -> str | None:
        path = self.root / name
        if not path.is_file():
            self.error(f"{name} is missing")
            return None
        return path.read_text(encoding="utf-8")

    def yaml(self, name: str):
        text = self.text(name)
        if text is None:
            return None
        for number, line in enumerate(text.splitlines(), 1):
            if "TODO" in line:
                self.error(f"{name}:{number}: unresolved TODO: {line.strip()}")
        try:
            return parse_yaml(text)
        except YamlError as exc:
            self.error(f"{name}: {exc}")
        return None

    # ---- toolchain, manifest, lakefile
    def check_toolchain(self) -> None:
        text = self.text("lean-toolchain")
        if text is not None:
            match = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc\d+)?\s*", text)
            if not match or int(match.group(1)) != 4 or int(match.group(2)) < 35:
                self.error(f"lean-toolchain: expected leanprover/lean4:v4.35.0 or later, found {text.strip()!r}")
        manifest_text = self.text("lake-manifest.json")
        lakefile = self.text("lakefile.lean")
        if manifest_text is None or lakefile is None:
            return
        try:
            manifest = json.loads(manifest_text)
            packages = {p["name"]: p for p in manifest["packages"]}
        except (json.JSONDecodeError, KeyError, TypeError) as exc:
            self.error(f"lake-manifest.json: unreadable: {exc}")
            return
        package = re.search(r"(?m)^package\s+(?:«([^»]+)»|(\w+))", lakefile)
        if package is None:
            self.error("lakefile.lean: no `package` declaration")
        elif manifest.get("name") != (package.group(1) or package.group(2)):
            self.error("lake-manifest.json: `name` differs from the package name of lakefile.lean")
        for name, entry in packages.items():
            if entry.get("type") != "git" or not str(entry.get("url", "")).startswith("https://"):
                self.error(f"lake-manifest.json: package {name} must be an https git dependency")
            if not HEX40.match(str(entry.get("rev", ""))):
                self.error(f"lake-manifest.json: package {name} has no 40-digit revision")
        requires = re.findall(r'require\s+(?:«([^»]+)»|(\w+))\s+from\s+git\s+"([^"]+)"\s*@\s*"([^"]+)"', lakefile)
        if not requires:
            self.error("lakefile.lean: no `require ... from git ... @ ...` found")
        for guillemets, plain, url, rev in requires:
            name = guillemets or plain
            entry = packages.get(name)
            if entry is None:
                self.error(f"lakefile.lean requires {name}, which lake-manifest.json does not list")
            elif entry.get("inputRev") != rev or (HEX40.match(rev) and entry.get("rev") != rev):
                self.error(f"lakefile.lean pins {name} at {rev}, lake-manifest.json has {entry.get('inputRev')}/{entry.get('rev')}")
            elif entry.get("url", "").removesuffix(".git") != url.removesuffix(".git"):
                self.error(f"lakefile.lean and lake-manifest.json disagree on the url of {name}")

    # ---- CITATION.cff and formalization.yaml
    def check_citation_and_formalization(self) -> dict | None:
        citation = self.yaml("CITATION.cff")
        formalization = self.yaml("formalization.yaml")
        if isinstance(citation, dict):
            for key in ("cff-version", "message", "title", "type", "authors", "license", "repository-code",
                        "abstract", "references"):
                if not citation.get(key):
                    self.error(f"CITATION.cff: `{key}` is missing")
            if citation.get("license") != "Apache-2.0":
                self.error("CITATION.cff: license must be Apache-2.0")
            if citation.get("repository-code") != REPOSITORY:
                self.error(f"CITATION.cff: repository-code must be {REPOSITORY}")
            if "date-released" in citation and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(citation["date-released"])):
                self.error("CITATION.cff: date-released must be YYYY-MM-DD")
            for author in citation.get("authors") or []:
                if not isinstance(author, dict) or not author.get("family-names") or not author.get("given-names"):
                    self.error("CITATION.cff: every author needs family-names and given-names")
        if not isinstance(formalization, dict):
            self.error("formalization.yaml: expected a mapping")
            return None
        if formalization.get("version") != "v0.4":
            self.error("formalization.yaml: version must be \"v0.4\"")
        project = formalization.get("project") or {}
        for key in ("name", "description", "authors", "responsible_maintainers", "affiliations", "license"):
            if not project.get(key):
                self.error(f"formalization.yaml: project.{key} is missing")
        if project.get("license") != "Apache-2.0":
            self.error("formalization.yaml: project.license must be Apache-2.0")
        if isinstance(citation, dict):
            cff_authors = {f"{a.get('given-names')} {a.get('family-names')}" for a in citation.get("authors") or []
                           if isinstance(a, dict)}
            if cff_authors != set(project.get("authors") or []):
                self.error("CITATION.cff and formalization.yaml list different authors")
        classification = formalization.get("classification") or {}
        for key in ("arxiv", "msc2020"):
            if not classification.get(key):
                self.error(f"formalization.yaml: classification.{key} is missing")
        if not formalization.get("sources"):
            self.error("formalization.yaml: sources is empty")
        for key in ("automation", "review"):
            if not formalization.get(key):
                self.error(f"formalization.yaml: `{key}` is missing (required by the v0.4 schema)")
        if not (formalization.get("review") or {}).get("status"):
            self.error("formalization.yaml: review.status is missing")
        methods = (formalization.get("automation") or {}).get("methods") or []
        if not methods:
            self.error("formalization.yaml: automation.methods is empty")
        for method in methods:
            if not isinstance(method, dict) or method.get("method") not in ENUMS["method"]:
                self.error(f"formalization.yaml: automation method must be one of {ENUMS['method']}")
        for source in formalization.get("sources") or []:
            if not isinstance(source, dict) or not source.get("title"):
                self.error("formalization.yaml: every source needs a `title`")
                continue
            for key in ("relationship", "author_endorsement"):
                if source.get(key) not in (None, *ENUMS[key]):
                    self.error(f"formalization.yaml: source `{source['title']}`: {key} must be one of {ENUMS[key]}")
        for related in formalization.get("related_formalizations") or []:
            if not isinstance(related, dict) or not related.get("id"):
                self.error("formalization.yaml: every related formalization needs an `id`")
            elif related.get("relationship") not in (None, *ENUMS["related"]):
                self.error(f"formalization.yaml: related formalization {related['id']}: relationship must be one of {ENUMS['related']}")
        status = formalization.get("status") or {}
        if status.get("sorry_count") != 0 or status.get("sorry_in_definitions") != 0:
            self.error("formalization.yaml: status must record sorry_count 0 and sorry_in_definitions 0")
        if not set(status.get("axioms") or []) <= STANDARD_AXIOMS:
            self.error(f"formalization.yaml: status.axioms must list only {sorted(STANDARD_AXIOMS)}")
        if not status.get("scope"):
            self.error("formalization.yaml: status.scope is missing")
        return status

    def check_main_results(self, status: dict | None) -> None:
        results = (status or {}).get("main_results")
        if not results:
            self.error("formalization.yaml: status.main_results is empty")
            return
        axioms_file = self.root / "scripts" / "Axioms.lean"
        printed = set(self.sources.PRINT_AXIOMS.findall(self.sources.code_mask(axioms_file.read_text(encoding="utf-8")))) \
            if axioms_file.is_file() else set()
        for entry in results:
            name, file = entry.get("declaration"), entry.get("file")
            if not name or not file:
                self.error("formalization.yaml: every main result needs `declaration` and `file`")
                continue
            path = self.root / file
            if not path.is_file():
                self.error(f"formalization.yaml: {name}: file {file} does not exist")
            elif name not in {n for _k, n, _e, _x in self.sources.declarations(path.read_text(encoding="utf-8"))}:
                self.error(f"formalization.yaml: {file} does not declare {name}")
            if entry.get("sorry_count") != 0:
                self.error(f"formalization.yaml: {name}: sorry_count must be 0")
            if not set(entry.get("axioms") or []) <= STANDARD_AXIOMS:
                self.error(f"formalization.yaml: {name}: axioms must be within {sorted(STANDARD_AXIOMS)}")
            config = entry.get("comparator_config")
            if config and not (self.root / config).is_file():
                self.error(f"formalization.yaml: {name}: comparator_config {config} does not exist")
            if name not in printed:
                self.error(f"formalization.yaml: {name} is not printed by scripts/Axioms.lean")

    # ---- documents
    def check_documents(self) -> None:
        license_text = self.text("LICENSE")
        if license_text is not None and not ("Apache License" in license_text and "Version 2.0" in license_text):
            self.error("LICENSE: not the Apache License, Version 2.0")
        for paper in PAPERS:
            pdf = self.root / paper
            if not pdf.is_file():
                self.error(f"{paper} is missing")
            elif pdf.read_bytes()[:5] != b"%PDF-":
                self.error(f"{paper} is not a PDF")
        self.text("docs/FORMALIZATION-NOTES.md")
        gitignore = self.text(".gitignore")
        if gitignore is not None and ".lake" not in gitignore:
            self.error(".gitignore: does not ignore .lake/")

    def comparator_names(self) -> set[str]:
        return {path.parent.name for path in (self.root / "Audit").glob("*/comparator.json")}

    def check_workflows(self) -> None:
        """Both workflows, read structurally; see the module docstring for what is required."""
        for file, title in (("build.yml", "Build and verify"), ("comparators.yml", "Comparators")):
            name = f".github/workflows/{file}"
            text = self.text(name)
            if text is None:
                continue
            for action, ref in re.findall(r"(?m)^\s*(?:-\s*)?uses:\s*(\S+?)@(\S+)", text):
                if not HEX40.match(ref):
                    self.error(f"{name}: {action}@{ref} is not pinned by a full commit hash")
            try:
                workflow = parse_yaml(text)
            except YamlError as exc:
                self.error(f"{name}: {exc}")
                continue
            if not isinstance(workflow, dict) or workflow.get("name") != title:
                self.error(f"{name}: the workflow must be named `{title}`")
                continue
            triggers = workflow.get("on")
            if not isinstance(triggers, dict) or "workflow_dispatch" not in triggers:
                self.error(f"{name}: no workflow_dispatch trigger")
            if re.search(r"cancel-in-progress:\s*true\b", text):
                self.error(f"{name}: cancel-in-progress must not be a constant true "
                           "(multi-hour runs are cancelled only for pull requests)")
            jobs = workflow.get("jobs") or {}
            if len(jobs) != 1:
                self.error(f"{name}: expected exactly one job")
                continue
            job = next(iter(jobs.values()))
            if job.get("timeout-minutes") != 360:
                self.error(f"{name}: the job's timeout-minutes must be 360, GitHub's limit for hosted jobs")
            steps = job.get("steps") or []
            names = [step.get("name") for step in steps]
            for step in steps:
                limit = step.get("timeout-minutes")
                if limit is not None and not (isinstance(limit, int) and limit <= 310):
                    self.error(f"{name}: step `{step.get('name')}` has timeout-minutes {limit}; "
                               "at most 310, so that setup and cache saving fit under the 360-minute job limit")
            if len(steps) < 2 or not str(steps[0].get("uses", "")).startswith("actions/checkout@"):
                self.error(f"{name}: the first step must be actions/checkout")
            if len(steps) < 2 or steps[1].get("name") != "Free runner disk space":
                self.error(f"{name}: `Free runner disk space` must be the step right after checkout")
            else:
                needed = 31457280 if file == "comparators.yml" else 20971520
                if f'-ge {needed}' not in str(steps[1].get("run", "")):
                    self.error(f"{name}: the free-space check must be `-ge {needed}` ({needed // 1048576} GiB)")
            if "Add swap" not in names:
                self.error(f"{name}: missing the `Add swap` step")
            if file == "build.yml":
                self.check_build_workflow(name, steps)
            else:
                self.check_comparators_workflow(name, steps, text, job)

    def check_build_workflow(self, name: str, steps: list) -> None:
        restore = [s for s in steps if str(s.get("uses", "")).startswith("actions/cache/restore@")]
        save = [s for s in steps if str(s.get("uses", "")).startswith("actions/cache/save@")]
        if len(restore) != 1 or len(save) != 1:
            self.error(f"{name}: expected one cache restore and one cache save step")
            return
        key = str((save[0].get("with") or {}).get("key", ""))
        for part in ("lake-build-", "github.sha", "github.run_id", "github.run_attempt"):
            if part not in key:
                self.error(f"{name}: the cache save key must contain `{part}` (one entry per attempt)")
        if key != str((restore[0].get("with") or {}).get("key", "")):
            self.error(f"{name}: the cache restore key must be the save key")
        if "always()" not in str(save[0].get("if", "")):
            self.error(f"{name}: the cache must be saved with `if: always()` (progress survives a timeout)")
        build = [s for s in steps if s.get("name") == "Build"]
        if len(build) != 1 or not isinstance(build[0].get("timeout-minutes"), int):
            self.error(f"{name}: the `Build` step needs its own timeout-minutes")

    def check_comparators_workflow(self, name: str, steps: list, text: str, job: dict) -> None:
        restore = [s for s in steps if str(s.get("uses", "")).startswith("actions/cache/restore@")]
        if len(restore) != 1:
            self.error(f"{name}: expected one cache restore step")
        else:
            options = restore[0].get("with") or {}
            if options.get("fail-on-cache-miss") is not True:
                self.error(f"{name}: the cache restore needs `fail-on-cache-miss: true` "
                           "(a cold build does not fit in this job)")
            if not str(options.get("key", "")).startswith("lake-build-"):
                self.error(f"{name}: the cache restore must use the build workflow's `lake-build-` entries")
        if "actions/cache/save@" in text:
            self.error(f"{name}: this workflow must not save a cache (it restores the build's)")
        if "lake build" in text.replace("lake-build", ""):
            self.error(f"{name}: this workflow must not build the library (restore the build's cache)")
        if "workflow_run" not in text:
            self.error(f"{name}: the workflow_run chaining (active or in the restore comment) is missing")
        names = [step.get("name") for step in steps]
        bubblewrap = [i for i, n in enumerate(names) if n and "bubblewrap" in n]
        comparator = [i for i, n in enumerate(names) if n and "lake comparator" in n]
        if not bubblewrap or not comparator or bubblewrap[0] > comparator[0]:
            self.error(f"{name}: bubblewrap must be installed before the comparator step")
        if "kernel.apparmor_restrict_unprivileged_userns=0" not in text:
            self.error(f"{name}: missing the AppArmor sysctl for bubblewrap")
        if "if" not in job:
            self.error(f"{name}: the job needs the `if:` condition on the build run's conclusion")
        matrix = ((job.get("strategy") or {}).get("matrix") or {}).get("comparator")
        if not isinstance(matrix, list) or set(matrix) != self.comparator_names() or len(matrix) != len(set(matrix)):
            self.error(f"{name}: strategy.matrix.comparator must list each Audit/<Name>/comparator.json once "
                       f"(found {matrix}, expected {sorted(self.comparator_names())})")

    def check_readme(self) -> None:
        text = self.text("README.md")
        if text is None:
            return
        for workflow in ("build.yml", "comparators.yml"):
            if f"actions/workflows/{workflow}" not in text:
                self.error(f"README.md: no badge for {workflow}")
        no_code = re.sub(r"```.*?```", "", text, flags=re.S)
        for target in re.findall(r"\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)", no_code):
            if re.match(r"(?:[a-z][a-z0-9+.-]*:|#)", target, re.I):
                continue
            relative = target.split("#")[0].split("?")[0]
            if relative and not (self.root / relative).exists():
                self.error(f"README.md: link target {relative} does not exist")
        self.check_readme_statements(text)

    def check_readme_statements(self, text: str) -> None:
        blocks = [b for b in re.findall(r"```lean[^\n]*\n(.*?)```", text, re.S)
                  if re.search(r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:theorem|lemma)\b", b)]
        if not blocks:
            return
        sources = {p: p.read_text(encoding="utf-8") for p in self.sources.lean_files(self.root)
                   if p.relative_to(self.root).parts[0] != "scripts"}
        for block in blocks:
            statement = block.strip("\n").rstrip()
            first = next(line for line in statement.splitlines() if re.search(r"\b(?:theorem|lemma)\b", line)).strip()
            holders = [(p, t) for p, t in sources.items() if statement in t]
            if not holders:
                self.error(f"README.md: the lean block `{first[:70]}` is not a verbatim piece of any Lean source")
                continue
            for path, source in holders:
                tail = source[source.index(statement) + len(statement):]
                if not re.match(r"\s*:=", tail):
                    self.error(f"README.md: the lean block `{first[:70]}` ends before the `:=` that begins the proof "
                               f"(in {path.relative_to(self.root).as_posix()})")

    def check_math(self) -> None:
        documents = [self.root / "README.md", *sorted((self.root / "docs").rglob("*.md"))]
        for path in documents:
            if not path.is_file():
                continue
            rel = path.relative_to(self.root).as_posix()
            text = path.read_text(encoding="utf-8")
            # Code blocks and inline code are not rendered as math; `$`...`$` and ```math are.
            prose = re.sub(r"```(?!math\n).*?```", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
            prose = re.sub(r"(?<!\$)`[^`\n]*`(?!\$)", lambda m: " " * len(m.group(0)), prose)
            for match in MATH_MACROS.finditer(prose):
                line = prose.count("\n", 0, match.start()) + 1
                self.error(f"{rel}:{line}: `{match.group(0)}` is not rendered by GitHub's math")
            for span in MATH_SPAN.finditer(prose):
                for tag in MATH_TAG.finditer(span.group(0)):
                    line = prose.count("\n", 0, span.start() + tag.start()) + 1
                    self.error(f"{rel}:{line}: `{tag.group(0)}` inside math is read as an HTML tag; "
                               r"write \lt or \gt, or add a space")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args(argv)
    checker = Metadata(args.root.resolve())
    checker.check_toolchain()
    status = checker.check_citation_and_formalization()
    checker.check_main_results(status)
    checker.check_documents()
    checker.check_workflows()
    checker.check_readme()
    checker.check_math()
    if checker.errors:
        print("check-metadata: FAIL")
        for error in checker.errors:
            print(f"- {error}")
        return 1
    print("check-metadata: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
