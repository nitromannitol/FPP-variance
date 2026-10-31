#!/usr/bin/env python3
"""Check the Lean sources of this repository before building (standard library only).

Usage: python3 scripts/check-lean-sources.py [--root DIR] [--max-lines N]

Every regular `.lean` file (all directories except `.git` and `.lake`) must

  * be a Lean module: `module` is the first token after ordinary comments
    (`lakefile.lean` is exempt);
  * have at most 10,000 physical lines (the registry limit) and be a regular
    file, not a symbolic link, in valid UTF-8;
  * contain none of `sorry`, `admit`, `axiom`, `opaque`, `set_option`,
    `native_decide`, `implemented_by`, `extern`, `unsafe` in code (comments and
    strings are ignored). The one exemption is `sorry` in the comparator
    challenges `Audit/<Name>/Challenge.lean`, where each theorem is stated with
    an intentional `sorry` (a count that differs from the number of theorems in
    the challenge's `comparator.json` is reported as a warning).

The libraries `CurvatureVariance` and `IsotropicVariance` must not import the
comparator library `Audit`.

Every comparator configuration is `Audit/<Name>/comparator.json`. It must name
the modules `Audit.<Name>.Challenge` and `Audit.<Name>.Solution` (both must
exist), list only theorems declared in both, permit only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), set `enable_nanoda` to true and
not set `external_kernels`. A Challenge has at most 1,000 lines and 100 KiB (a
review warning above 300 lines or 32 KiB), no `private` declaration, and every
definition exposed (`@[expose]`, or one `@[expose] public section`); a Solution
has no `private` declaration either.

Axiom audit coverage: `scripts/Axioms.lean` must print the axioms of every
theorem of `CurvatureVariance/Statements/` and `IsotropicVariance/Statements/`
(the main theorems, the cited results and the companion theorems), of every
theorem the comparator configurations name, and of every theorem the README
lists (a `theorem` in a `lean` block, or a declared theorem named in backticks).

Exit status: 0 PASS, 1 FAIL.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

MAX_LINES = 10_000
CHALLENGE_MAX_LINES, CHALLENGE_MAX_BYTES = 1_000, 100 * 1024
CHALLENGE_REVIEW_LINES, CHALLENGE_REVIEW_BYTES = 300, 32 * 1024
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMPARATOR_KEYS = {"challenge_module", "solution_module", "theorem_names", "definition_names",
                   "permitted_axioms", "enable_nanoda"}
SKIP_DIRS = {".git", ".lake"}
LIBRARIES = ("CurvatureVariance", "IsotropicVariance")
AUDIT = "Audit"

MODULE_KEYWORD = re.compile(r"module(?![\w'.!?])")
CHAR_LITERAL = re.compile(r"'(?:\\.|[^\\'\n])'")
IDENT = r"(?:[A-Za-z_][A-Za-z0-9_'!?]*|«[^»\n]+»)"
NAME = rf"{IDENT}(?:\.{IDENT})*"
NAMESPACE = re.compile(rf"^[ \t]*namespace[ \t]+({NAME})")
SECTION = re.compile(
    rf"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*((?:(?:public|private|noncomputable)[ \t]+)*)section(?:[ \t]+{NAME})?[ \t]*$")
END = re.compile(rf"^[ \t]*end(?:[ \t]+{NAME})?[ \t]*$")
DECL = re.compile(
    r"^[ \t]*(?:(?:open|set_option)\b[^\n]*?\bin[ \t]+)*((?:@\[[^\]\n]*\][ \t]*)*)"
    r"((?:(?:private|protected|public|meta|noncomputable|unsafe|partial|nonrec|scoped|local)[ \t]+)*)"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|axiom)\b"
    rf"(?:[ \t]+({NAME}))?")
FORBIDDEN_TOKEN = re.compile(
    r"(?<![\w.'])(sorry|admit|axiom|opaque|set_option|native_decide|implemented_by|extern|unsafe)(?![\w'])")
IMPORT_OF = re.compile(r"(?m)^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(\S+)[ \t]*$")
PRIVATE_WORD = re.compile(r"(?<![\w.'])private(?![\w'])")
EXPOSE_SECTION = re.compile(r"@\[[^\]\n]*\bexpose\b[^\]\n]*\][ \t]*public[ \t]+section")
PRINT_AXIOMS = re.compile(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+(\S+)")


def header_token_offset(text: str) -> int:
    """Offset of the first token after ordinary comments and whitespace.

    A doc comment `/-- -/` or a module doc `/-! -/` is a command, not a comment,
    so it ends the scan: it cannot precede `module`.
    """
    index, size = 0, len(text)
    while index < size:
        if text[index].isspace() or text[index] == "﻿":
            index += 1
        elif text.startswith("--", index):
            newline = text.find("\n", index)
            index = size if newline < 0 else newline + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            depth, index = 1, index + 2
            while index < size and depth:
                if text.startswith("/-", index):
                    depth, index = depth + 1, index + 2
                elif text.startswith("-/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
        else:
            return index
    return size


def has_module_header(text: str) -> bool:
    return MODULE_KEYWORD.match(text, header_token_offset(text)) is not None


def code_mask(text: str) -> str:
    """Blank comments (doc comments included) and string literals, keeping offsets and newlines."""
    out = list(text)
    index, size = 0, len(text)

    def blank(start: int, end: int) -> None:
        for position in range(start, end):
            if out[position] != "\n":
                out[position] = " "

    while index < size:
        if text.startswith("--", index):
            end = text.find("\n", index)
            end = size if end < 0 else end
            blank(index, end)
            index = end
        elif text.startswith("/-", index):
            start, depth, index = index, 1, index + 2
            while index < size and depth:
                if text.startswith("/-", index):
                    depth, index = depth + 1, index + 2
                elif text.startswith("-/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
            blank(start, index)
        elif (text[index] == "'" and CHAR_LITERAL.match(text, index)
              and not (index and (text[index - 1].isalnum() or text[index - 1] in "_'!?"))):
            index = CHAR_LITERAL.match(text, index).end()
        elif text[index] == '"':
            start, index = index, index + 1
            while index < size and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
            index = min(index + 1, size)
            blank(start, index)
        else:
            index += 1
    return "".join(out)


def declarations(text: str) -> list[tuple[str, str, bool, bool]]:
    """(kind, full name, exported, attributes on the line) for each named top-level declaration.

    In a module a declaration is exported when it is marked `public`, or lies in a
    `public section`, and is not `private`.
    """
    module = has_module_header(text)
    namespaces: list[str] = []
    scopes: list[tuple[int, str | None]] = []
    found: list[tuple[str, str, bool, bool]] = []
    for line in code_mask(text).splitlines():
        if match := NAMESPACE.match(line):
            parts = match.group(1).split(".")
            namespaces.extend(parts)
            scopes.append((len(parts), None))
        elif match := SECTION.match(line):
            words = match.group(1).split()
            scopes.append((0, "public" if "public" in words else "private" if "private" in words else None))
        elif END.match(line):
            if scopes:
                count, _ = scopes.pop()
                if count:
                    del namespaces[-count:]
        elif match := DECL.match(line):
            attributes, modifiers = match.group(1), match.group(2).split()
            kind, name = match.group(3), match.group(4)
            if name is None:
                continue
            default = next((v for _c, v in reversed(scopes) if v is not None), "private" if module else "public")
            exported = "private" not in modifiers and ("public" in modifiers or default == "public")
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join([*namespaces, name])
            found.append((kind, full, exported, bool(attributes and "expose" in attributes)))
    return found


def lean_files(root: Path) -> list[Path]:
    files = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(d for d in subdirectories
                                   if d not in SKIP_DIRS and not (Path(directory) / d).is_symlink())
        files.extend(Path(directory) / name for name in sorted(names) if name.endswith(".lean"))
    return files


def module_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def physical_lines(text: str) -> int:
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


class Checker:
    def __init__(self, root: Path, max_lines: int) -> None:
        self.root = root
        self.max_lines = max_lines
        self.errors: list[str] = []
        self.warnings: list[str] = []
        self.texts: dict[str, str] = {}
        self.challenge_paths: dict[str, int] = {}  # Challenge file -> number of configured theorems
        self.solution_paths: set[str] = set()
        self.intentional_sorries: dict[str, int] = {}

    def rel(self, path: Path) -> str:
        return path.relative_to(self.root).as_posix()

    def error(self, message: str) -> None:
        self.errors.append(message)

    # ------------------------------------------------------------------ comparator

    def comparator_configs(self) -> list[Path]:
        found = []
        for directory, subdirectories, names in os.walk(self.root, followlinks=False):
            subdirectories[:] = sorted(d for d in subdirectories if d not in SKIP_DIRS)
            found.extend(Path(directory) / n for n in names if n == "comparator.json")
        return sorted(found)

    def read_config(self, config: Path) -> dict | None:
        rel = self.rel(config)
        try:
            data = json.loads(config.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            self.error(f"{rel}: unreadable: {exc}")
            return None
        if not isinstance(data, dict):
            self.error(f"{rel}: expected a JSON object")
            return None
        return data

    def expected_modules(self, config: Path) -> tuple[str, str] | None:
        parts = config.relative_to(self.root).parts
        if len(parts) != 3 or parts[0] != AUDIT:
            self.error(f"{self.rel(config)}: comparator configurations live at {AUDIT}/<Name>/comparator.json")
            return None
        return f"{AUDIT}.{parts[1]}.Challenge", f"{AUDIT}.{parts[1]}.Solution"

    def check_comparator(self, config: Path) -> set[str]:
        """Check one configuration; returns the theorem names it selects."""
        rel = self.rel(config)
        data = self.read_config(config)
        expected = self.expected_modules(config)
        if data is None or expected is None:
            return set()
        for key in sorted(set(data) - COMPARATOR_KEYS):
            if key == "external_kernels":
                self.error(f"{rel}: external_kernels is not a submitter field")
            else:
                self.warnings.append(f"{rel}: unknown key {key}")
        names = data.get("theorem_names")
        if not isinstance(names, list) or not names or not all(isinstance(n, str) and n for n in names):
            self.error(f"{rel}: theorem_names must be a nonempty list of names")
            names = []
        challenge, solution = expected
        if data.get("challenge_module") != challenge:
            self.error(f"{rel}: challenge_module must be {challenge}")
        if data.get("solution_module") != solution:
            self.error(f"{rel}: solution_module must be {solution}")
        self.challenge_paths[self.rel(module_path(self.root, challenge))] = len(names)
        self.solution_paths.add(self.rel(module_path(self.root, solution)))
        definitions = data.get("definition_names", [])
        if not isinstance(definitions, list) or not all(isinstance(n, str) and n for n in definitions):
            self.error(f"{rel}: definition_names must be a list of names")
            definitions = []
        axioms = data.get("permitted_axioms")
        if not isinstance(axioms, list) or not set(axioms) <= STANDARD_AXIOMS:
            self.error(f"{rel}: permitted_axioms must name only {sorted(STANDARD_AXIOMS)}")
        if data.get("enable_nanoda") is not True:
            self.error(f"{rel}: enable_nanoda must be true")
        for module, label in ((challenge, "Challenge"), (solution, "Solution")):
            path = module_path(self.root, module)
            if not path.is_file():
                self.error(f"{rel}: the {label} module {module} has no file {self.rel(path)}")
                continue
            declared = {name for _k, name, _e, _x in declarations(self.read(path))}
            for name in [*names, *definitions]:
                if name not in declared:
                    self.error(f"{rel}: {name} is not declared in the {label} source")
        return {n for n in names if isinstance(n, str)}

    def read(self, path: Path) -> str:
        key = self.rel(path)
        if key not in self.texts:
            try:
                self.texts[key] = path.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as exc:
                self.error(f"{key}: unreadable: {exc}")
                self.texts[key] = ""
        return self.texts[key]

    def check_challenge(self, path: Path) -> None:
        rel = self.rel(path)
        text = self.read(path)
        lines, size = physical_lines(text), len(text.encode("utf-8"))
        if lines > CHALLENGE_MAX_LINES or size > CHALLENGE_MAX_BYTES:
            self.error(f"{rel}: Challenge has {lines} lines and {size} bytes "
                       f"(limit {CHALLENGE_MAX_LINES} lines, {CHALLENGE_MAX_BYTES} bytes)")
        elif lines > CHALLENGE_REVIEW_LINES or size > CHALLENGE_REVIEW_BYTES:
            self.warnings.append(f"{rel}: Challenge has {lines} lines and {size} bytes "
                                 f"(review threshold {CHALLENGE_REVIEW_LINES} lines, {CHALLENGE_REVIEW_BYTES} bytes)")
        masked = code_mask(text)
        if not EXPOSE_SECTION.search(masked):
            lines_masked = masked.splitlines()
            for number, line in enumerate(lines_masked):
                match = DECL.match(line)
                if not match or match.group(3) in ("theorem", "lemma") or match.group(4) is None:
                    continue
                previous = lines_masked[number - 1] if number else ""
                if "expose" not in (match.group(1) or "") and not re.fullmatch(r"\s*@\[[^\]]*\bexpose\b[^\]]*\]\s*", previous):
                    self.error(f"{rel}:{number + 1}: definition {match.group(4)} is not exposed "
                               f"(use @[expose], or one @[expose] public section)")
        configured = self.challenge_paths.get(rel, 0)
        found = self.intentional_sorries.get(rel, 0)
        if found != configured:
            self.warnings.append(f"{rel} has {found} sorry but its comparator.json names {configured} theorems "
                                 f"(expected one sorry per theorem)")

    # ------------------------------------------------------------------ files

    def check_file(self, path: Path) -> None:
        rel = self.rel(path)
        if path.is_symlink():
            self.error(f"{rel}: must be a regular Lean file, not a symbolic link")
            return
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            self.error(f"{rel}: source is not valid UTF-8")
            return
        self.texts[rel] = text
        if path.name != "lakefile.lean" and not has_module_header(text):
            self.error(f"{rel}: not a module (the first token after comments must be `module`)")
        lines = physical_lines(text)
        if lines > self.max_lines:
            self.error(f"{rel}: {lines} lines exceeds {self.max_lines}; split into smaller modules")
        masked = code_mask(text)
        if path.name != "lakefile.lean" and FORBIDDEN_TOKEN.search(masked):
            for number, line in enumerate(masked.splitlines(), 1):
                for match in FORBIDDEN_TOKEN.finditer(line):
                    word = match.group(1)
                    if word == "sorry" and rel in self.challenge_paths:
                        self.intentional_sorries[rel] = self.intentional_sorries.get(rel, 0) + 1
                    else:
                        self.error(f"{rel}:{number}: `{word}` in code")
        if rel.split("/")[0].removesuffix(".lean") in LIBRARIES:
            for imported in IMPORT_OF.findall(masked):
                if imported.split(".")[0] == AUDIT:
                    self.error(f"{rel}: the library must not import {imported}")
        if (rel in self.solution_paths or rel in self.challenge_paths) and PRIVATE_WORD.search(masked):
            self.error(f"{rel}: `private` in a Challenge or Solution file (breaks matching by dependency closure)")

    # ------------------------------------------------------------------ axiom audit coverage

    def theorems_in(self, path: Path) -> list[str]:
        return [name for kind, name, _e, _x in declarations(self.read(path)) if kind in ("theorem", "lemma")]

    def readme_theorems(self, readme: Path, sources: list[Path], prefixes: set[str]) -> set[str]:
        text = readme.read_text(encoding="utf-8")
        shorts: set[str] = set()
        for block in re.findall(r"```lean[^\n]*\n(.*?)```", text, re.S):
            for match in re.finditer(rf"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:theorem|lemma)[ \t]+({NAME})", block):
                shorts.add(match.group(1))
        quoted = set(re.findall(rf"`({NAME})`", text))
        if not shorts and not quoted:
            return set()
        lasts = {name.rsplit(".", 1)[-1] for name in shorts | quoted}
        hit = re.compile(r"\b(?:theorem|lemma)[ \t]+[\w.'«»]*?(?:" + "|".join(re.escape(n) for n in sorted(lasts)) + r")\b")
        declared: set[str] = set()
        for path in sources:
            if hit.search(self.read(path)):
                declared.update(self.theorems_in(path))

        def candidates(name: str) -> set[str]:
            return {c for c in (name, *(f"{prefix}.{name}" for prefix in prefixes)) if c in declared}

        required: set[str] = set()
        for short in sorted(shorts):
            options = candidates(short)
            if not options:
                self.error(f"README.md lists theorem {short}, which no Lean source declares")
            required |= options
        for name in sorted(quoted):
            required |= candidates(name)
        return required

    def check_axiom_coverage(self, configured: set[str], files: list[Path]) -> None:
        axioms_file = self.root / "scripts" / "Axioms.lean"
        if not axioms_file.is_file():
            self.error("scripts/Axioms.lean is missing")
            return
        printed = set(PRINT_AXIOMS.findall(code_mask(self.read(axioms_file))))
        required: dict[str, str] = {}
        for library in LIBRARIES:
            statements = self.root / library / "Statements"
            if not statements.is_dir():
                self.error(f"{library}/Statements/ is missing")
                continue
            for path in sorted(statements.rglob("*.lean")):
                for name in self.theorems_in(path):
                    required.setdefault(name, self.rel(path))
        for name in sorted(configured):
            required.setdefault(name, "comparator.json")
        prefixes = {*LIBRARIES, *(name.rsplit(".", 1)[0] for name in configured if "." in name)}
        readme = self.root / "README.md"
        if readme.is_file():
            for name in sorted(self.readme_theorems(readme, files, prefixes)):
                required.setdefault(name, "README.md")
        else:
            self.error("README.md is missing")
        for name, origin in sorted(required.items()):
            if name not in printed:
                self.error(f"scripts/Axioms.lean does not print the axioms of {name} (listed in {origin})")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--max-lines", type=int, default=MAX_LINES)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    checker = Checker(root, args.max_lines)
    configs = checker.comparator_configs()
    if not configs:
        checker.error(f"no comparator configuration {AUDIT}/<Name>/comparator.json")
    configured: set[str] = set()
    for config in configs:
        configured |= checker.check_comparator(config)
    files = lean_files(root)
    for path in files:
        checker.check_file(path)
    for rel in sorted(checker.challenge_paths):
        if (root / rel).is_file():
            checker.check_challenge(root / rel)
    checker.check_axiom_coverage(configured, files)
    for warning in checker.warnings:
        print(f"warning: {warning}")
    summary = f"{len(files)} Lean files, {len(configs)} comparator configurations"
    sorries = sum(checker.intentional_sorries.values())
    if sorries:
        summary += f", {sorries} intentional sorries in the Challenges"
    if checker.errors:
        print(f"check-lean-sources: FAIL ({summary})")
        for error in checker.errors:
            print(f"- {error}")
        return 1
    print(f"check-lean-sources: PASS ({summary})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
