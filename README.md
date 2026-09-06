# Ten math.CO papers formalized in Lean

This repository contains ten end-to-end formalization developments selected
from the 1 September 2026 arXiv `math.CO` listing. The only direct Lean
dependency is [mathlib](https://github.com/leanprover-community/mathlib4),
pinned together with Lean to `v4.31.0`.

See [INDEX.md](INDEX.md) for the papers, public entry points, and precise
completion status. Each first-level directory under [`LeanCo/`](LeanCo/)
contains exactly one paper development. [`LeanCo.lean`](LeanCo.lean) is the
single aggregate import.

## Contributors

This project was developed by [Jing Jia](https://jjia131.github.io/),
[Guanyang Wang](https://guanyangwang.github.io/), and
[Peng Zhang](https://sites.google.com/site/pengzhang27182/).

## Build

Install Lean's `elan` toolchain manager, then run these commands from the
repository root. The Lean version is selected by `lean-toolchain`, and the
dependency revisions are recorded in `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

To check a single paper during development, build its entry module, for example:

```bash
lake build LeanCo.InversionDescent.EndToEnd
```

The frozen rejection sample and its offline replay script are kept in
[`Sampling/`](Sampling/). Replay the sample with Python 3:

```bash
python3 Sampling/rejection_sample_mathco.py --trace
```

## License

Copyright 2026 Jing Jia, Guanyang Wang, and Peng Zhang.

This repository is licensed under the [Apache License 2.0](LICENSE).

The adapted Baker--Norine proof retains its upstream attribution and license
in [`LeanCo/LaplacianLFunctions/BakerNorine/`](LeanCo/LaplacianLFunctions/BakerNorine/).
