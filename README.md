# Resonance Kinetics in Lean

Formal proofs of collision invariants, spectral gaps, closed collision forms, and Onsager transport structure for four-wave resonance models.

Developed and maintained by **[veridiscoverLab](https://github.com/veridiscoverLab)**.

This release contains **690 Lean modules and 4,992 explicit theorems**. Its mathematical sources are byte-for-byte identical to a snapshot that passed a clean project build, theorem-type and dependency audits, and a replay of every imported declaration from an empty Lean kernel. The source manifest and verification evidence are included.

## Verified main results

| Result | Scope |
|---|---|
| **Measurable collision-invariant classification** | For the one-dimensional pinned dispersion $\omega_d(x)=\sqrt{1-2d\cos x}$, $0<d<1/2$, every finite-valued, almost-everywhere measurable collision invariant is uniquely $A+B\omega_d$. Smoothness is a conclusion. |
| **Pinned-chain spectral gap** | The full weighted resonance dissipation has a positive gap away from the two-dimensional invariant space. The gap and the required compactness are proved. |
| **Maximal closed form and self-adjoint realization** | The maximal full collision-difference operator is closed and densely defined, with the correctly normalized nonnegative self-adjoint realization, domain, kernel, and form gap. |
| **Exact Onsager degeneracy** | The actual fifteen-source transport tensor has a **seven-dimensional kernel and rank eight**, with uniform two-sided bounds on compact positive Rayleigh--Jeans parameter sets. Reciprocity and nonnegativity are proved. |
| **Five-moment linear decay** | The original constant-parameter system has quantitative Fourier-mode decay and a real Sobolev evolution on the torus, including uniform mean-zero decay. |

[Theorem statements and Lean entry points](docs/THEOREMS.md) explain the exact objects, assumptions, and conclusions. [Mathematical overview](docs/MATHEMATICAL_OVERVIEW.md) describes the mechanisms behind the proofs.

The library also contains the original sharp-cube resonance measure, five-moment classification, weighted coercivity, cell inverses, local positive kinetic solutions, moment-matching entropy identities, and parts of the nonlinear limit argument.

## Manuscript

[Read the English PDF](paper/output/pdf/resonance_kinetic_en.pdf) · [LaTeX source](paper/main.tex) · [Build instructions](paper/README.md)

*Collision invariants of a pinned chain and macroscopic transport in truncated wave kinetics* contains the full mathematical proofs, including the nonlinear Euler limit and first-order transport laws. The final nonlinear results remain on the formalization [roadmap](docs/ROADMAP.md); their status is distinguished from the verified main results above.

## Build

Install [Lean through elan](https://github.com/leanprover/elan), Git, and Python 3.10 or newer. The checked-in toolchain and Lake lockfile pin the dependencies.

```sh
git clone https://github.com/veridiscoverLab/resonance-kinetic-lean.git
cd resonance-kinetic-lean
lake exe cache get
lake build Resonance
```

The toolchain is **Lean 4.29.0**. Mathlib is pinned to commit [`8a178386ffc0f5fef0b77738bb5449d50efeea95`](https://github.com/leanprover-community/mathlib4/tree/8a178386ffc0f5fef0b77738bb5449d50efeea95).

## Verify

```sh
# Check the frozen source inventory and hashes.
python3 scripts/verify.py --source-only

# Build, inspect theorem types, and audit the actual proof dependency cone.
python3 scripts/verify.py

# Also replay every imported declaration from an empty Lean kernel.
python3 scripts/verify.py --fresh
```

The current publication audit covers **9,160 theorem roots and 82,345 constants**, including private and generated theorem roots. It has **zero unsafe or partial dependencies**. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

See [verification procedure and trust boundary](docs/VERIFICATION.md), the [source manifest](verification/manifest.json), the [current publication check](verification/publication-check.json), and the separate [historical verification summary](verification/historical/summary.json). The documented comparison accounts for six additional generated roots in the current audit. Kernel replay uses Lean's own checker; it is not a second independently implemented proof assistant. Theorem alignment with the stated mathematics is documented separately from successful compilation.

## Further work

The main results above are verified. The **full nonlinear hydrodynamic limit on an entire prescribed Euler window and the final strong-current/first-order transport theorem are not yet completely formalized in this release**. They are tracked in the [roadmap](docs/ROADMAP.md), with [paper-level derivations and their explicit dependencies](docs/PROOF_NOTES.md).

This repository does not claim a formal derivation from NLS or a complete solution of Hilbert's sixth problem.

## Repository layout

```text
Resonance/                 Mathematical Lean sources
Resonance.lean             Complete verified-library import
docs/                     English mathematics, scope, and roadmap
paper/                    English manuscript, LaTeX source, and compiled PDF
scripts/verify.py          Portable verification driver
verification/manifest.json Source hashes and declaration inventory
verification/historical/   Evidence for the fully replayed snapshot
```

The working drafts and the later, partially audited extensions are not included in the default library. This keeps the published build aligned with its completed verification evidence.

## Attribution

The project contributor and maintainer is **veridiscoverLab**. See [CONTRIBUTORS.md](CONTRIBUTORS.md), [CITATION.cff](CITATION.cff), and [NOTICE.md](NOTICE.md).
