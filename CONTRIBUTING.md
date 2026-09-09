# Contributing

This project is maintained by [veridiscoverLab](https://github.com/veridiscoverLab).

Before changing a proof, identify the exact theorem statement and the original mathematical object it concerns. Preserve parameter ranges, quantifier order, measures, domains, normalization factors, and the dependence of uniform constants.

## Proof changes

- Keep the full four-leg resonance relation and its common measure. Auxiliary coordinates need proved links to the original objects.
- Do not introduce `sorry`, admissions, custom mathematical axioms, or unchecked proof dependencies.
- An existence, compactness, coercivity, or convergence conclusion must not reappear as a hidden structure field or an additional hypothesis of the advertised main theorem.
- Use separate declarations for conditional intermediate results, and state the remaining obligations explicitly.
- Keep the toolchain and dependencies pinned. A dependency update requires a new verification record.

## Verification records

The current manifest is a frozen release inventory. An intentional source change should fail its hash check until a new reviewed manifest is prepared. Never rewrite historical evidence to describe a changed source tree.

A new verified snapshot requires its exact source inventory, successful build, inspected root types, a dependency-cone audit, and a completed fresh-kernel replay. Document the mathematical scope independently of those checks. Update the roadmap when an original target, rather than only an intermediate lemma, has been completed.

See [docs/VERIFICATION.md](docs/VERIFICATION.md) for the executable procedure.
