# Roadmap

Maintained by veridiscoverLab.

This release contains the fully replayed 690-module snapshot, with 4,992
explicit theorems. Its verification claim concerns the declarations and
dependencies in that snapshot. It does **not** establish an end-to-end formal
proof of every statement in the accompanying mathematical program.

The ten items below describe requirements absent from this release. Some
supporting lemmas are already shipped; their presence does not prove the
composed result. Work outside the release, including separately checked
extensions, is not counted as part of its verification evidence.

[Proof notes](PROOF_NOTES.md) explain conditional mathematical implications
behind these requirements. They are not additional Lean certificates.

## 1. A common nonlinear corrector along an Euler path

Construct one moment-compatible nonlinear corrector for every point of the
prescribed positive Euler window and every sufficiently large collision rate.
Prove compatibility of local parameter constructions, their required time and
space derivatives, the critical weighted integral estimates, the original
equation residual, and the nonzero corrector initial layer.

**Release boundary:** the small nonlinear cell and substantial linear
parameter-resolvent infrastructure are present. The required uniform nonlinear
parameter derivatives and their complete substitution into the PDE corrector
are not established by the release.

**Completion criterion:** a theorem about the same corrector field supplies
its equation, all five zero moments, derivative bounds, residual bounds, and
initial error. Smooth selection and a small residual must be conclusions.

## 2. Complete localized nonlinear coercivity

Combine the actual diagonal coefficient with every off-diagonal contribution
of the original four-leg collision derivative. Allow a fixed positive ratio
bound in a shrinking corner layer and require small deviation only outside
that layer.

**Release boundary:** the complete derivative split, off-diagonal estimates,
and several original conditional role-mass estimates are present. The full
localized nonlinear coercivity theorem is not.

**Completion criterion:** obtain constants uniform on the specified positive
parameter compact set without assuming the desired diagonal positivity,
coercivity, or globally small corner amplitude.

## 3. The full third-order coframe energy estimate

Use the actual moment-matched coordinates of the same kinetic solution.
Control every nonlinear product, moving projection, connection coefficient,
highest parameter derivative, and lower-order coupling in the joint
microscopic and macroscopic energy.

**Release boundary:** exact evolution identities and individual product
estimates do not yet yield the complete absorption estimate.

**Completion criterion:** derive

$$
 E'(t)+\gamma c D(t)
 \le C E(t)+C\Lambda^{3/2}c^{-3/2}
$$

with fixed positive order weights, no uncontrolled highest derivative norm,
and no remaining term of size `c E`. The inequality must follow from the
original collision operator, rather than appear as a final theorem input.

## 4. Joint corner-source bounds

Complete the source estimates in the positive exchange decomposition:
vanishing inverse-frequency-weighted rows for the corrector, square-row
estimates for the error, the common spatial supremum, and the time integral.

**Release boundary:** original kernel and frequency results provide inputs;
the complete source estimate along the actual solution is not shipped.

**Completion criterion:** prove a common `L1(time; Linfinity(space,corner))`
bound with the original opposite and adjacent leg identities. Separate
pointwise estimates or unweighted row compactness are insufficient.

## 5. All corners and the bulk amplitude estimate

Transport the comparison argument to all eight corners and combine it with
the complementary bulk estimate. Coordinate reflections must act on all
four momenta, with the physical velocity retained in the transformed
characteristics.

**Completion criterion:** the same solution satisfies improved positive
upper and lower corner bounds and an improved small bulk error throughout
the provisional window. A reflected function cannot simply be declared a
solution of an unchanged transport equation.

## 6. Continuation through a prescribed positive Euler window

Fix the constants in their required order, combine items 1--5, exclude a
first exit, and apply continuation to the same initial-value problem. Then
derive the sharper macroscopic second-order Sobolev estimate from the actual
five-moment flux equation.

**Completion criterion:** for an arbitrary prescribed finite positive smooth
Euler window, prove the kinetic comparison with a collision-rate threshold
chosen before the solution. Recover the `c^(-3/4)` third-order error and
`c^(-1)` second-order macroscopic error with their stated norms. Temporary
bootstrap assumptions must be removed at the endpoint.

## 7. Nonlinear Euler existence and higher regularity

Construct the positive five-moment Euler solution in the claimed Sobolev
class, including approximation, a common positive time interval, convergence,
uniqueness, and strong time continuity. Prove any stated kinetic spatial
regularity beyond the already constructed class.

**Release boundary:** a constant-coefficient Fourier evolution and a
third-order kinetic local theory do not establish nonlinear Euler local
existence or arbitrary finite-order regularity.

**Completion criterion:** derive these results from the original parameter
domain and coefficients. A comparison theorem conditional on a given smooth
Euler window does not also construct that window.

## 8. Entropy work from actual error estimates

Identify the entropy work with its integral on the common time-space-momentum
measure. Use the actual coframe error estimates to prove strong convergence
of the dual forcing, and use all five matching constraints to remove the
reference parameter time derivative.

**Release boundary:** the original current norm and exact initial-to-terminal
entropy balance are present; the work limit derived from the full dynamics is
not.

**Completion criterion:** prove convergence of the work to the cell energy.
Do not assume work convergence in the final strong-current theorem, or use
terminal entropy convergence before it has been derived.

## 9. Strong current and all fifteen first-order fluxes

Combine the actual weak cell identification, entropy norm limit, recovery of
the five-dimensional kernel, and the physical adjoint return. Identify all
three spatial fluxes of all five moments on the same full time window.

**Completion criterion:** derive strong convergence of the signed complete
resonance current and the first-order transport remainder
`o(c^(-1))` in `L2(time; H^(-1)(space))`. Preserve the distinction between
frequency-weighted and unweighted physical spaces. Neither scaled initial
trace convergence nor globally small corner ratios may be added silently.

## 10. Target alignment and complete release verification

For every newly completed root theorem, compare its elaborated type with the
intended mathematical statement, including domain, quantifier order,
normalization, constants, exclusions, and endpoint conventions. Check that
all substantial hypotheses hold for the actual object supplied to it.

**Completion criterion:** ship an immutable source manifest, a clean build,
complete declaration and dependency inventories, permitted-axiom checks, and
a complete import replay from an initially empty kernel. Incomplete runs or
checks of a later, unshipped source tree cannot certify this release.

## Dependency order

Items 1--5 supply the inputs to item 6. Item 7 is a separate construction
requirement: it cannot be inferred from a comparison with a given Euler
solution. Items 8--9 depend on the actual full-window bounds from item 6.
Item 10 applies to each completed stage and to their final composition.

No item is complete merely because its conclusion follows from a conditional
estimate recorded in the proof notes. The estimate's hypotheses must also be
proved for the original solution family.
