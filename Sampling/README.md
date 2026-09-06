# Audit for the offline ten-paper rejection sample

This is the frozen audit contract for the deterministic ten-paper sample from
the 1 September 2026 arXiv `math.CO` listing.  The sampler itself performs no
network requests.  It replays the frozen population, v1 page metadata, and
pre-existing-Lean audit recorded in this repository.

Replay it from the repository root with:

```bash
python3 Sampling/rejection_sample_mathco.py --trace
```

## Eligibility rule

A proposal is accepted exactly when all four conditions hold:

1. the article is a `new` submission in the frozen `math.CO` listing, which
   means its primary category is `math.CO`, rather than a cross-list;
2. its v1 manuscript has at most 25 pages;
3. the bounded public audit below did not find a Lean formalization that
   existed before this repository selected the paper; and
4. its arXiv ID has not already been accepted in this run.

## Sampling scope

For every at-most-25-page primary proposal reached through counter 38, the
audit checked the official arXiv v1 record and ancillary files, exact-ID and
title web searches, GitHub repository search, and the 1 September 2026
Papers With Lean snapshot.

## Final accepted sequence

| Rank | Counter | arXiv ID | v1 pages |
|---:|---:|---|---:|
| 1 | 1 | `2608.30266` | 9 |
| 2 | 5 | `2608.30481` | 10 |
| 3 | 13 | `2608.30180` | 8 |
| 4 | 20 | `2608.30053` | 7 |
| 5 | 21 | `2608.29201` | 22 |
| 6 | 29 | `2608.29203` | 15 |
| 7 | 30 | `2608.30544` | 6 |
| 8 | 33 | `2608.29163` | 16 |
| 9 | 34 | `2608.29224` | 18 |
| 10 | 38 | `2608.29981` | 10 |
