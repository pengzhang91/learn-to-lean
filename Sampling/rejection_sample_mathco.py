#!/usr/bin/env python3
"""Reproduce the 2026-09-01 math.CO rejection sample without networking.

The proposal at counter ``c`` is derived as follows::

    digest = SHA256(seed.encode("utf-8") + b":" + str(c).encode("ascii"))
    x = int.from_bytes(digest, "big")

The digest is first rejected when it lies in the incomplete tail of the
256-bit range.  Otherwise, ``x % N`` selects a row of the frozen population.
Proposals are made with replacement.  A selected row is accepted exactly
when its listing section is ``new`` (rather than ``cross``), its frozen v1
page count is at most the configured limit, the frozen bounded public audit
did not find a pre-existing Lean formalization, and its arXiv ID has not
already been accepted in this run.

This program never contacts arXiv and never downloads a PDF.  Page counts and
Lean-audit decisions are read from separate frozen TSV files.  Only records
reached by the counter stream are required; a missing reached record is a
fatal, explicit error rather than an implicit rejection.  A negative Lean
audit means only "not found in the documented bounded public search"; it is
not a proof that no private or unindexed formalization exists.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence


DATA_DIR = Path(__file__).resolve().parent
DEFAULT_POPULATION = DATA_DIR / "arxiv_population_2026-09-01.tsv"
DEFAULT_METADATA = DATA_DIR / "arxiv_metadata_2026-09-01.tsv"
DEFAULT_LEAN_AUDIT = DATA_DIR / "arxiv_lean_audit_2026-09-02.tsv"
DEFAULT_SEED = (
    "b63d35dd5d05a3d9c2043fdc71f15d99868ff01e82292b3e92f18fd8c3cf0411"
)
DEFAULT_POPULATION_SHA256 = (
    "31df2dac5a97f293925a8c023af78f3a92804416cd3c314fe9d427f17f26b71e"
)
DEFAULT_METADATA_SHA256 = (
    "eaca5ebed7488eb207fec5abe7a271d87674036ed6b843727769a749dafa7d62"
)
DEFAULT_LEAN_AUDIT_SHA256 = (
    "2eb52cb6d09f76ad724b320c19ee4f5c006d809b28e6b0650406c47eb3c111a9"
)
DEFAULT_EXPECTED_PREFIX = (
    "2608.30266",
    "2608.30481",
    "2608.30180",
    "2608.30053",
    "2608.29201",
    "2608.29203",
    "2608.30544",
    "2608.29163",
    "2608.29224",
    "2608.29981",
)
ARXIV_ID_RE = re.compile(r"^[0-9]{4}\.[0-9]{4,5}$")
LEAN_NOT_FOUND = "not_found_in_bounded_public_search"
LEAN_FOUND = "found_existing_lean"


class SamplingError(RuntimeError):
    """An input or sampling invariant was violated."""


@dataclass(frozen=True)
class Paper:
    ordinal: int
    section: str
    arxiv_id: str
    title: str


@dataclass(frozen=True)
class Attempt:
    counter: int
    digest: str
    index: int | None
    ordinal: int | None
    arxiv_id: str | None
    section: str | None
    v1_pages: int | None
    preexisting_lean_status: str | None
    decision: str


@dataclass(frozen=True)
class Acceptance:
    rank: int
    counter: int
    digest: str
    index: int
    ordinal: int
    arxiv_id: str
    v1_pages: int
    preexisting_lean_status: str
    title: str


def _read_tsv(path: Path, required_columns: set[str]) -> tuple[list[dict[str, str]], str]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise SamplingError(f"cannot read {path}: {exc.strerror or exc}") from exc

    checksum = hashlib.sha256(raw).hexdigest()
    try:
        text = raw.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise SamplingError(f"{path} is not valid UTF-8: {exc}") from exc

    try:
        reader = csv.DictReader(io.StringIO(text), delimiter="\t")
        if reader.fieldnames is None:
            raise SamplingError(f"{path} has no TSV header")
        fieldnames = {name.strip() for name in reader.fieldnames if name is not None}
        missing = sorted(required_columns - fieldnames)
        if missing:
            raise SamplingError(
                f"{path} is missing required column(s): {', '.join(missing)}"
            )

        rows: list[dict[str, str]] = []
        for line_number, raw_row in enumerate(reader, start=2):
            if None in raw_row:
                raise SamplingError(
                    f"{path}:{line_number} has more fields than the TSV header"
                )
            row = {key.strip(): (value or "").strip() for key, value in raw_row.items()}
            if not any(row.values()):
                continue
            row["__line__"] = str(line_number)
            rows.append(row)
    except csv.Error as exc:
        raise SamplingError(f"cannot parse TSV {path}: {exc}") from exc
    return rows, checksum


def load_population(path: Path) -> tuple[list[Paper], str]:
    rows, checksum = _read_tsv(
        path, {"ordinal", "section", "arxiv_id", "title"}
    )
    if not rows:
        raise SamplingError(f"population {path} is empty")

    papers: list[Paper] = []
    seen_ids: set[str] = set()
    for expected_ordinal, row in enumerate(rows, start=1):
        line_number = row["__line__"]
        try:
            ordinal = int(row["ordinal"])
        except ValueError as exc:
            raise SamplingError(
                f"{path}:{line_number} has a non-integer ordinal: {row['ordinal']!r}"
            ) from exc
        if ordinal != expected_ordinal:
            raise SamplingError(
                f"{path}:{line_number} has ordinal {ordinal}; expected {expected_ordinal}"
            )

        section = row["section"]
        if section not in {"new", "cross"}:
            raise SamplingError(
                f"{path}:{line_number} has unknown section {section!r}; "
                "expected 'new' or 'cross'"
            )
        arxiv_id = row["arxiv_id"]
        if not ARXIV_ID_RE.fullmatch(arxiv_id):
            raise SamplingError(
                f"{path}:{line_number} has invalid arXiv ID {arxiv_id!r}"
            )
        if arxiv_id in seen_ids:
            raise SamplingError(
                f"{path}:{line_number} repeats arXiv ID {arxiv_id}"
            )
        if not row["title"]:
            raise SamplingError(f"{path}:{line_number} has an empty title")

        seen_ids.add(arxiv_id)
        papers.append(Paper(ordinal, section, arxiv_id, row["title"]))
    return papers, checksum


def load_metadata(
    path: Path, population_by_id: dict[str, Paper]
) -> tuple[dict[str, int], str]:
    rows, checksum = _read_tsv(
        path,
        {
            "arxiv_id",
            "version",
            "primary_category",
            "v1_pages",
            "page_source",
            "source_url",
            "checked_at_utc",
        },
    )
    pages_by_id: dict[str, int] = {}
    for row in rows:
        line_number = row["__line__"]
        arxiv_id = row["arxiv_id"]
        if not ARXIV_ID_RE.fullmatch(arxiv_id):
            raise SamplingError(
                f"{path}:{line_number} has invalid arXiv ID {arxiv_id!r}"
            )
        if arxiv_id not in population_by_id:
            raise SamplingError(
                f"{path}:{line_number} contains {arxiv_id}, which is not in the population"
            )
        if arxiv_id in pages_by_id:
            raise SamplingError(
                f"{path}:{line_number} repeats arXiv ID {arxiv_id}"
            )
        if row["version"] != "v1":
            raise SamplingError(
                f"{path}:{line_number} has version {row['version']!r}; expected 'v1'"
            )
        primary_category = row["primary_category"]
        listed_as_primary = population_by_id[arxiv_id].section == "new"
        metadata_is_primary = primary_category == "math.CO"
        if listed_as_primary != metadata_is_primary:
            raise SamplingError(
                f"{path}:{line_number} disagrees with the frozen listing for {arxiv_id}: "
                f"section={population_by_id[arxiv_id].section!r}, "
                f"primary_category={primary_category!r}"
            )
        if not row["page_source"] or not row["source_url"] or not row["checked_at_utc"]:
            raise SamplingError(
                f"{path}:{line_number} has incomplete page-count provenance"
            )
        try:
            pages = int(row["v1_pages"])
        except ValueError as exc:
            raise SamplingError(
                f"{path}:{line_number} has a non-integer v1_pages value: "
                f"{row['v1_pages']!r}"
            ) from exc
        if pages <= 0:
            raise SamplingError(
                f"{path}:{line_number} has non-positive v1_pages {pages}"
            )
        pages_by_id[arxiv_id] = pages
    return pages_by_id, checksum


def load_lean_audit(
    path: Path, population_by_id: dict[str, Paper]
) -> tuple[dict[str, str], str]:
    rows, checksum = _read_tsv(
        path,
        {
            "arxiv_id",
            "preexisting_lean_status",
            "arxiv_v1_lean_hit",
            "paperswithlean_2026-09-01_hit",
            "github_repo_exact_id_hits",
            "web_exact_search_lean_hit",
            "evidence_url",
        },
    )
    status_by_id: dict[str, str] = {}
    boolean_columns = (
        "arxiv_v1_lean_hit",
        "paperswithlean_2026-09-01_hit",
        "web_exact_search_lean_hit",
    )

    for row in rows:
        line_number = row["__line__"]
        arxiv_id = row["arxiv_id"]
        if not ARXIV_ID_RE.fullmatch(arxiv_id):
            raise SamplingError(
                f"{path}:{line_number} has invalid arXiv ID {arxiv_id!r}"
            )
        if arxiv_id not in population_by_id:
            raise SamplingError(
                f"{path}:{line_number} contains {arxiv_id}, which is not in the population"
            )
        if population_by_id[arxiv_id].section != "new":
            raise SamplingError(
                f"{path}:{line_number} audits non-primary row {arxiv_id}"
            )
        if arxiv_id in status_by_id:
            raise SamplingError(f"{path}:{line_number} repeats arXiv ID {arxiv_id}")

        status = row["preexisting_lean_status"]
        if status not in {LEAN_NOT_FOUND, LEAN_FOUND}:
            raise SamplingError(
                f"{path}:{line_number} has unknown preexisting_lean_status "
                f"{status!r}"
            )

        hit_flags: list[bool] = []
        for column in boolean_columns:
            value = row[column]
            if value not in {"true", "false"}:
                raise SamplingError(
                    f"{path}:{line_number} has non-boolean {column}={value!r}"
                )
            hit_flags.append(value == "true")
        try:
            github_hits = int(row["github_repo_exact_id_hits"])
        except ValueError as exc:
            raise SamplingError(
                f"{path}:{line_number} has non-integer github_repo_exact_id_hits="
                f"{row['github_repo_exact_id_hits']!r}"
            ) from exc
        if github_hits < 0:
            raise SamplingError(
                f"{path}:{line_number} has negative GitHub hit count {github_hits}"
            )

        any_public_hit = any(hit_flags) or github_hits > 0
        if (status == LEAN_FOUND) != any_public_hit:
            raise SamplingError(
                f"{path}:{line_number} has status {status!r} inconsistent with "
                "its recorded public-search hits"
            )
        if not row["evidence_url"]:
            raise SamplingError(
                f"{path}:{line_number} has no Lean-audit evidence URL"
            )
        status_by_id[arxiv_id] = status

    return status_by_id, checksum


def rejection_sample(
    population: Sequence[Paper],
    pages_by_id: dict[str, int],
    lean_status_by_id: dict[str, str],
    *,
    seed: str,
    count: int,
    max_pages: int,
    max_counters: int,
) -> tuple[list[Acceptance], list[Attempt], int]:
    """Return distinct acceptances, the full trace, and counters consumed."""

    if not population:
        raise SamplingError("cannot sample an empty population")
    if count <= 0:
        raise SamplingError("count must be positive")
    if max_pages <= 0:
        raise SamplingError("max-pages must be positive")
    if max_counters <= 0:
        raise SamplingError("max-counters must be positive")

    primary_count = sum(paper.section == "new" for paper in population)
    if count > primary_count:
        raise SamplingError(
            f"cannot accept {count} distinct primary papers from only "
            f"{primary_count} section=new rows"
        )

    n = len(population)
    range_size = 1 << 256
    unbiased_limit = range_size - (range_size % n)
    accepted: list[Acceptance] = []
    accepted_ids: set[str] = set()
    attempts: list[Attempt] = []

    for counter in range(max_counters):
        digest_bytes = hashlib.sha256(f"{seed}:{counter}".encode("utf-8")).digest()
        digest = digest_bytes.hex()
        value = int.from_bytes(digest_bytes, "big")

        if value >= unbiased_limit:
            attempts.append(
                Attempt(
                    counter,
                    digest,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    "reject_range",
                )
            )
            continue

        index = value % n
        paper = population[index]
        common = (counter, digest, index, paper.ordinal, paper.arxiv_id, paper.section)

        if paper.section != "new":
            attempts.append(Attempt(*common, None, None, "reject_wrong_primary"))
            continue
        if paper.arxiv_id in accepted_ids:
            attempts.append(
                Attempt(
                    *common,
                    pages_by_id.get(paper.arxiv_id),
                    lean_status_by_id.get(paper.arxiv_id),
                    "reject_duplicate",
                )
            )
            continue

        try:
            pages = pages_by_id[paper.arxiv_id]
        except KeyError as exc:
            raise SamplingError(
                f"metadata is missing v1_pages for reached primary paper "
                f"{paper.arxiv_id} (counter {counter}, population index {index})"
            ) from exc
        if pages > max_pages:
            attempts.append(Attempt(*common, pages, None, "reject_over_page_limit"))
            continue

        try:
            lean_status = lean_status_by_id[paper.arxiv_id]
        except KeyError as exc:
            raise SamplingError(
                f"Lean audit is missing for reached page-eligible primary paper "
                f"{paper.arxiv_id} (counter {counter}, population index {index})"
            ) from exc
        if lean_status == LEAN_FOUND:
            attempts.append(
                Attempt(*common, pages, lean_status, "reject_existing_lean")
            )
            continue

        attempts.append(Attempt(*common, pages, lean_status, "accept"))
        accepted_ids.add(paper.arxiv_id)
        accepted.append(
            Acceptance(
                rank=len(accepted) + 1,
                counter=counter,
                digest=digest,
                index=index,
                ordinal=paper.ordinal,
                arxiv_id=paper.arxiv_id,
                v1_pages=pages,
                preexisting_lean_status=lean_status,
                title=paper.title,
            )
        )
        if len(accepted) == count:
            return accepted, attempts, counter + 1

    raise SamplingError(
        f"counter limit {max_counters} reached after accepting "
        f"{len(accepted)} of {count} requested papers"
    )


def _escape_markdown(value: object) -> str:
    if value is None:
        return ""
    return str(value).replace("\\", "\\\\").replace("|", "\\|").replace("\n", " ")


def _markdown_table(headers: Sequence[str], rows: Iterable[Sequence[object]]) -> str:
    lines = [
        "| " + " | ".join(headers) + " |",
        "|" + "|".join("---" for _ in headers) + "|",
    ]
    lines.extend(
        "| " + " | ".join(_escape_markdown(value) for value in row) + " |"
        for row in rows
    )
    return "\n".join(lines)


def _print_human(
    accepted: Sequence[Acceptance],
    attempts: Sequence[Attempt],
    *,
    show_trace: bool,
    population_sha256: str,
    metadata_sha256: str,
    lean_audit_sha256: str,
    seed: str,
    max_pages: int,
    counters_consumed: int,
) -> None:
    print(
        f"Accepted {len(accepted)} distinct papers in {counters_consumed} counters "
        f"(section=new, v1_pages<={max_pages}, no pre-existing Lean found)."
    )
    print(f"seed: {seed}")
    print(f"population_sha256: {population_sha256}")
    print(f"metadata_sha256: {metadata_sha256}")
    print(f"lean_audit_sha256: {lean_audit_sha256}")

    if show_trace:
        print("\nCounter trace\n")
        print(
            _markdown_table(
                (
                    "counter",
                    "digest",
                    "index",
                    "arXiv ID",
                    "section",
                    "pages",
                    "pre-existing Lean audit",
                    "decision",
                ),
                (
                    (
                        attempt.counter,
                        attempt.digest,
                        attempt.index,
                        attempt.arxiv_id,
                        attempt.section,
                        attempt.v1_pages,
                        attempt.preexisting_lean_status,
                        attempt.decision,
                    )
                    for attempt in attempts
                ),
            )
        )

    print("\nAccepted papers\n")
    print(
        _markdown_table(
            (
                "rank",
                "counter",
                "index",
                "ordinal",
                "arXiv ID",
                "pages",
                "pre-existing Lean audit",
                "title",
            ),
            (
                (
                    item.rank,
                    item.counter,
                    item.index,
                    item.ordinal,
                    item.arxiv_id,
                    item.v1_pages,
                    item.preexisting_lean_status,
                    item.title,
                )
                for item in accepted
            ),
        )
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Offline, deterministic rejection sampling from the frozen "
            "2026-09-01 arXiv math.CO listing."
        )
    )
    parser.add_argument(
        "--population",
        type=Path,
        default=DEFAULT_POPULATION,
        help=f"population TSV (default: {DEFAULT_POPULATION})",
    )
    parser.add_argument(
        "--metadata",
        type=Path,
        default=DEFAULT_METADATA,
        help=f"TSV with arxiv_id and v1_pages (default: {DEFAULT_METADATA})",
    )
    parser.add_argument(
        "--lean-audit",
        type=Path,
        default=DEFAULT_LEAN_AUDIT,
        help=(
            "TSV with frozen pre-existing-Lean search decisions "
            f"(default: {DEFAULT_LEAN_AUDIT})"
        ),
    )
    parser.add_argument("--seed", default=DEFAULT_SEED, help="recorded UTF-8 seed")
    parser.add_argument("--count", type=int, default=10, help="distinct papers to accept")
    parser.add_argument(
        "--max-pages", type=int, default=25, help="inclusive v1 page limit"
    )
    parser.add_argument(
        "--max-counters",
        type=int,
        default=1_000_000,
        help="safety bound on SHA-256 counters consumed",
    )
    parser.add_argument(
        "--trace", action="store_true", help="include every counter decision"
    )
    parser.add_argument(
        "--json", action="store_true", help="emit stable JSON instead of Markdown tables"
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    try:
        population, population_sha256 = load_population(args.population)
        if args.population.resolve() == DEFAULT_POPULATION.resolve():
            if population_sha256 != DEFAULT_POPULATION_SHA256:
                raise SamplingError(
                    "default population checksum mismatch: expected "
                    f"{DEFAULT_POPULATION_SHA256}, got {population_sha256}"
                )
        population_by_id = {paper.arxiv_id: paper for paper in population}
        pages_by_id, metadata_sha256 = load_metadata(args.metadata, population_by_id)
        if args.metadata.resolve() == DEFAULT_METADATA.resolve():
            if metadata_sha256 != DEFAULT_METADATA_SHA256:
                raise SamplingError(
                    "default metadata checksum mismatch: expected "
                    f"{DEFAULT_METADATA_SHA256}, got {metadata_sha256}"
                )
        lean_status_by_id, lean_audit_sha256 = load_lean_audit(
            args.lean_audit, population_by_id
        )
        if args.lean_audit.resolve() == DEFAULT_LEAN_AUDIT.resolve():
            if lean_audit_sha256 != DEFAULT_LEAN_AUDIT_SHA256:
                raise SamplingError(
                    "default Lean-audit checksum mismatch: expected "
                    f"{DEFAULT_LEAN_AUDIT_SHA256}, got {lean_audit_sha256}"
                )
        accepted, attempts, counters_consumed = rejection_sample(
            population,
            pages_by_id,
            lean_status_by_id,
            seed=args.seed,
            count=args.count,
            max_pages=args.max_pages,
            max_counters=args.max_counters,
        )

        canonical_fixture = (
            population_sha256 == DEFAULT_POPULATION_SHA256
            and metadata_sha256 == DEFAULT_METADATA_SHA256
            and lean_audit_sha256 == DEFAULT_LEAN_AUDIT_SHA256
            and args.seed == DEFAULT_SEED
            and args.max_pages == 25
        )
        if canonical_fixture:
            prefix_length = min(len(accepted), len(DEFAULT_EXPECTED_PREFIX))
            actual_prefix = tuple(item.arxiv_id for item in accepted[:prefix_length])
            expected_prefix = DEFAULT_EXPECTED_PREFIX[:prefix_length]
            if actual_prefix != expected_prefix:
                raise SamplingError(
                    "canonical fixture prefix mismatch: expected "
                    f"{expected_prefix}, got {actual_prefix}"
                )

        if args.json:
            payload: dict[str, object] = {
                "schema_version": 2,
                "config": {
                    "seed": args.seed,
                    "count": args.count,
                    "max_pages": args.max_pages,
                    "primary_listing_section": "new",
                    "preexisting_lean_rule": LEAN_NOT_FOUND,
                    "unique_acceptances": True,
                    "population_size": len(population),
                    "population_sha256": population_sha256,
                    "metadata_sha256": metadata_sha256,
                    "lean_audit_sha256": lean_audit_sha256,
                    "counters_consumed": counters_consumed,
                },
                "accepted": [asdict(item) for item in accepted],
            }
            if args.trace:
                payload["attempts"] = [asdict(attempt) for attempt in attempts]
            json.dump(payload, sys.stdout, ensure_ascii=False, indent=2)
            sys.stdout.write("\n")
        else:
            _print_human(
                accepted,
                attempts,
                show_trace=args.trace,
                population_sha256=population_sha256,
                metadata_sha256=metadata_sha256,
                lean_audit_sha256=lean_audit_sha256,
                seed=args.seed,
                max_pages=args.max_pages,
                counters_consumed=counters_consumed,
            )
    except SamplingError as exc:
        parser.exit(2, f"error: {exc}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
