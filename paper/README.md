# Manuscript

**Collision invariants of a pinned chain and macroscopic transport in truncated wave kinetics**

Author: **veridiscoverLab**.

[Read the English PDF](output/pdf/resonance_kinetic_en.pdf).

The manuscript includes the collision-invariant classification and closed form for the one-dimensional pinned chain, and the Euler limit, Onsager tensor and first-order transport laws for the sharply truncated three-dimensional wave kinetic equation. It contains the full paper proofs.

Formal verification is tracked separately by [theorem entry points](../docs/THEOREMS.md) and the [verification guide](../docs/VERIFICATION.md). The nonlinear Euler-interval limit and final strong-current theorem are paper results whose end-to-end formalization remains on the [roadmap](../docs/ROADMAP.md).

## Build

Use Tectonic 0.17.0 or latexmk with XeLaTeX. The manuscript uses standard LaTeX packages and TeX Gyre Termes; no CJK fonts are needed.

```sh
sh build.sh
```

To select a particular Tectonic executable:

```sh
TECTONIC=/path/to/tectonic sh build.sh
```

Intermediate files are written to `build/`. The PDF is written to `output/pdf/resonance_kinetic_en.pdf`.
