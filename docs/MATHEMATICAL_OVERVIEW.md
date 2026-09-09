# Mathematical overview

The verified release develops two collision geometries and follows each through to its stated conclusions. For the one-dimensional pinned chain, the conclusions are measurable invariant classification, a full resonance spectral gap, and a maximal closed form with its self-adjoint realization. For the three-dimensional cube model, the principal conclusions highlighted here are the exact degeneracy of the fifteen-dimensional Onsager tensor and decay of the frozen five-moment system.

The two dispersions, momentum spaces, and resonance measures remain distinct. Within each model, every construction uses the same complete quartet relation. Auxiliary charts, pair kernels, and moment coordinates are proved representations of that relation; they do not replace it with independently chosen collisions. Precise statements and final declaration names are listed in the [theorem catalogue](THEOREMS.md).

## From measurable invariants to rigidity on the circle

For the pinned dispersion

$$
\omega_d(x)=\sqrt{1-2d\cos x},\qquad 0<d<\tfrac12,
$$

the invariant equation is

$$
\varphi(x)+\varphi(y)-\varphi(z)-\varphi(x+y-z)=0
$$

on the full periodic energy-resonance surface. The first difficulty is that the input is only almost-everywhere measurable. Differentiating it is not initially legitimate, and restricting an almost-everywhere identity to a selected curve is not automatic.

The proof first constructs genuine transverse charts of the original energy equation. Each relevant source coordinate has a nonvanishing derivative with respect to the averaging variable. This gives quantitative domination of the source-coordinate pushforward measures. Explicit quartets handle the special target points where the simpler symmetric charts degenerate. The constructions retain circle periodicity and all momentum branches. See [PinnedCharts.lean](../Resonance/PinnedCharts.lean) and [PinnedJacobian.lean](../Resonance/PinnedJacobian.lean).

Finite measurable functions have level sets $\{|\varphi|>M\}$ whose measure tends to zero. In a chart, the three source-coordinate bounds ensure that a common set of averaging variables avoids all three large-value sets. The complete invariant identity then bounds the target value. This proves local essential boundedness without first assuming $L^1$ integrability. That argument is formalized in [PinnedMeasurable.lean](../Resonance/PinnedMeasurable.lean).

Once local integrability is available, the same identity is averaged against a smooth compactly supported function. Changes of variables in the source terms produce smooth integral kernels, and local representatives can be joined into a global smooth periodic representative. The transfer from completed-measurable data is handled explicitly; the proof does not identify a completed-measurable function with a Borel function pointwise. See [PinnedGlobalRegularity.lean](../Resonance/PinnedGlobalRegularity.lean), [PinnedAERegularity.lean](../Resonance/PinnedAERegularity.lean), and [PinnedInvariantTransfer.lean](../Resonance/PinnedInvariantTransfer.lean).

Rigidity is then obtained by differentiating an actual symmetric resonance branch. Second-order identities eliminate the odd component. A third-order compatibility identity constrains the even component, while the endpoint and periodic matching conditions exclude the remaining singular local candidate. The result is exactly $A+B\omega_d$. The differential identities are derived from the original four-term equation, rather than assumed as a surrogate definition of invariance. The calculation and its global conclusion are in [PinnedElimination.lean](../Resonance/PinnedElimination.lean), [PinnedODE.lean](../Resonance/PinnedODE.lean), and [PinnedClassification.lean](../Resonance/PinnedClassification.lean).

## Why classification yields a gap only after compactness

A finite-dimensional nullspace alone does not imply a positive spectral gap. The formalization additionally proves compactness for sequences whose **full quartet energy** tends to zero.

A finite cover by target intervals $I_j$ gives smoothing averages $K_j$ whose combined defect is controlled by the original complete difference:

$$
\sum_j\|f-K_jf\|_{L^2(I_j)}^2\le C\int|\Delta f|^2\,d\Xi_d.
$$

The source estimates give compactness of the averaged functions along one common subsequence for the finite cover. A bounded sequence with energy tending to zero therefore has a strongly convergent $L^2$ subsequence. The construction averages the same function in every chart and bounds all errors by the same full resonance measure. See [PinnedFullAverageEnergy.lean](../Resonance/PinnedFullAverageEnergy.lean), [PinnedFiniteAverages.lean](../Resonance/PinnedFiniteAverages.lean), and [PinnedLpCompactness.lean](../Resonance/PinnedLpCompactness.lean).

Passing the invariant equation to the limit requires absolute continuity of **all four** coordinate marginals of the full regular coarea measure with respect to circle Haar measure. This is proved on the entire regular surface, not just on the finite averaging charts. The critical sets of coordinate projections are controlled using the actual pinned velocity level sets. The final bridge is [PinnedLegACCircle.lean](../Resonance/PinnedLegACCircle.lean).

If a gap failed, one could take unit vectors orthogonal to $1$ and $\omega_d$ with energy tending to zero. Compactness produces a unit limit, full-marginal absolute continuity and Fatou's lemma give zero full energy, and invariant classification puts the limit in the excluded two-dimensional space. This contradiction establishes the gap in [PinnedGap.lean](../Resonance/PinnedGap.lean). A positive lower bound on a quartet weight transfers the unweighted gap to the weighted form.

## Cancellation, maximal domains, and self-adjointness

The resonance measure can be singular near trivial quartets. Estimating the four terms separately would lose the cancellation needed for finite energy. Near a trivial pairing, suitable local coordinates give the simultaneous factorizations

$$
F_d=-uv\,G_{\omega_d},\qquad
\Delta\varphi=-uv\,G_\varphi,
$$

where $G_\varphi$ is bounded by second derivatives of $\varphi$. The complete numerator therefore cancels the dangerous factors of the energy constraint. The different critical cases are covered explicitly. This yields finite energy for $C^2$ periodic functions in [PinnedFiniteEnergy.lean](../Resonance/PinnedFiniteEnergy.lean).

Define the difference operator on its maximal domain: an $L^2$ function belongs to the domain precisely when its complete four-term difference lies in the weighted resonance $L^2$ space. The four marginal absolute-continuity results make the operator independent of the chosen $L^2$ representative. They also allow simultaneous almost-everywhere subsequences in a closed-graph proof. See [PinnedMaximalDifference.lean](../Resonance/PinnedMaximalDifference.lean).

Smooth circle functions are dense in the source $L^2$ space, and the finite-energy result places them in the maximal domain. These two facts give a densely defined closed operator. The density result is proved for the actual probability Haar measure in [SmoothCircleDensity.lean](../Resonance/SmoothCircleDensity.lean).

Finally, orthogonal projection onto the closed graph constructs the resolvent needed for the nonnegative self-adjoint operator $R^*R$. Applying this to $\sqrt{\gamma/4}\,R$ gives the exact normalization $(\gamma/4)R^*R$. This is a proved representation theorem, not an added self-adjointness assumption. See [ClosedOperatorRepresentation.lean](../Resonance/ClosedOperatorRepresentation.lean) and [PinnedOperator.lean](../Resonance/PinnedOperator.lean). The argument concerns the full maximal form domain; it does not assert a smooth form core.

## The cube model: geometric degeneracy and weighted coercivity

The cube model has momentum domain $D_R=[-R,R]^3$, quadratic energy $|k|^2$, and the five collision invariants

$$
\Psi=(1,k_1,k_2,k_3,|k|^2).
$$

Every quartet retains all four cube constraints together with momentum and energy conservation. Exact changes of variables identify the same complete collision measure with useful sphere and plane representations. The global measure identities, including sharp boundaries, are in [CoareaGlobal.lean](../Resonance/CoareaGlobal.lean) and [PlaneGlobal.lean](../Resonance/PlaneGlobal.lean).

The collision frequency degenerates at the eight corners. If $r$ measures distance to the corner set, the proved small-distance scale is

$$
\nu_*(k)\asymp r(k)^2\log^2\!\frac{C}{r(k)}.
$$

The logarithms arise from the actual one-axis product densities and the full signed convolution of three axes. The proof first identifies that convolution with the original fixed-output frequency, including boundary outputs. See [CubeFrequencyReflection.lean](../Resonance/CubeFrequencyReflection.lean) and [CornerFrequencyBounds.lean](../Resonance/CornerFrequencyBounds.lean).

This scale has two useful consequences. The critical inverse power $\nu_*^{-3/2}$ is integrable, and the weighted Newton energy needed for pair-kernel compactness is finite. Both statements concern the original cube measure; values at the eight zero-frequency points are treated through the proved measure-zero statement. See [CornerInverseFrequency.lean](../Resonance/CornerInverseFrequency.lean) and [CornerNewtonEnergy.lean](../Resonance/CornerNewtonEnergy.lean).

The natural Hilbert norm is consequently frequency weighted. Compactness of the actual pair operators, the full five-invariant classification, and the preserved positive collision form give coercivity on the microscopic subspace. The finite-rank projection is still the extension of the original unweighted volume projection onto $N_\theta\Psi$; changing the norm does not change its definition. These identifications lead to actual weak and bounded-source cell solutions in [PhysicalVariationalCell.lean](../Resonance/PhysicalVariationalCell.lean), [BoundedCellSource.lean](../Resonance/BoundedCellSource.lean), and [StrongBoundedCell.lean](../Resonance/StrongBoundedCell.lean).

## Moment matching and relative entropy

The five moments also organize the entropy geometry of the same distribution. Let $f>0$ almost everywhere with $f\in L^1(D_R)$, and let $N=N_\theta$ and $\bar N=N_{\bar\theta}$ have strictly positive denominators on the closed cube. If
$\int_{D_R}\Psi f=\int_{D_R}\Psi N$, define the nonnegative, possibly infinite relative entropy by

$$
\mathscr H(f\mid N)=\int_{D_R}\left(\frac fN-1-\log\frac fN\right)\,dk.
$$

The exact decomposition is

$$
\mathscr H(f\mid\bar N)=\mathscr H(f\mid N)+\mathscr H(N\mid\bar N).
$$

The cross term vanishes because it is precisely a linear combination of the five matched moments:

$$
\int_{D_R}(f-N)(\bar N^{-1}-N^{-1})\,dk
=(\bar\theta-\theta)\cdot\int_{D_R}\Psi(f-N)\,dk=0.
$$

All these moment integrals are finite under the stated assumptions. The extended-entropy theorem does not assume $\log f\in L^1$, so the Pythagorean identity includes infinite entropy. With that additional logarithmic integrability, the ordinary finite-integral three-point identity is also proved. The exact cube declarations are `Entropy.cube_entropy_pythagoras_extended` and `Entropy.cube_entropy_threepoint` in [Entropy.lean](../Resonance/Entropy.lean).

For spatially dependent distributions, the matching condition applies at each spatial point before integrating in space. This decomposition separates microscopic mismatch from the displacement of the matched moments, using the same $f$, $N$, and $\bar N$. It supplies the zero-order entropy geometry for nonlinear analysis; it does not by itself prove higher Sobolev estimates or the full-window nonlinear limit.

## Why the Onsager tensor has rank eight

The tensor is formed by solving those cell problems for the fifteen projected drives $Q_\theta(2k_iN_\theta\Psi_A)$. Its quadratic form is a collision-form square, so it vanishes exactly when the corresponding projected drive vanishes.

Before projection, a direction $(a,B,h)$ produces

$$
2N_\theta(k)\bigl(a\cdot k+k^TBk+|k|^2h\cdot k\bigr).
$$

Membership in the five-dimensional collision kernel is therefore an actual polynomial identity on the cube. Its cubic terms force $h=0$, and its quadratic terms force $\operatorname{Sym}B$ to be scalar. The linear vector $a$, the three-dimensional skew part of $B$, and its scalar symmetric part contribute seven null directions. The complementary eight directions have positive response.

The polynomial identity is proved from almost-everywhere equality on the original cube; it is not a sampled or numerical rank computation. See [OnsagerPolynomial.lean](../Resonance/OnsagerPolynomial.lean), [ActualOnsagerNullDirections.lean](../Resonance/ActualOnsagerNullDirections.lean), and [ActualOnsagerRank.lean](../Resonance/ActualOnsagerRank.lean).

Continuity of the actual cell family and the exact fixed nullspace give a uniform positive bound on the effective quotient over each compact positive parameter set. This is the mechanism behind the quantitative deviatoric bounds in [ActualOnsagerUniform.lean](../Resonance/ActualOnsagerUniform.lean).

## How degenerate dissipation still produces decay

For a nonzero spatial Fourier direction, the Onsager symbol has an undamped mass direction. Positive definiteness of the dissipative symbol on all five components would therefore be false. The frozen Euler flux matrices couple that direction to the dissipative components.

A compensating quadratic term combines the conservative and dissipative parts. The resulting energy is uniformly comparable to the original moment-Gram energy and decays at rate

$$
\frac{c|\ell|^2}{c^2+|\ell|^2}.
$$

The mode calculation is returned to the original $M_\theta$, $J_{\theta,i}$, and $\mathsf K_\theta$, retaining the same time variable and collision parameter $c$. See [ActualCompensatedDecay.lean](../Resonance/ActualCompensatedDecay.lean) and [ActualOriginalModeDecay.lean](../Resonance/ActualOriginalModeDecay.lean).

Fourier synthesis then constructs the Sobolev evolution. Its coefficients preserve the conjugation relation that characterizes real data. The construction proves the initial trace and the original PDE in two fewer Sobolev derivatives; it does not stop at an estimate for a hypothetical solution. Removing the zero mode gives uniform $e^{-a t/c}$ decay for $c\ge1$. The final real-valued statements are in [ActualRealSobolevPDE.lean](../Resonance/ActualRealSobolevPDE.lean).

## Boundary of the verified conclusions

The release verifies these collision-geometry, operator, tensor, and frozen-evolution results for their stated original objects. It does not establish the complete nonlinear kinetic-to-Euler limit over a prescribed Euler window or the final strong first-order nonlinear collision-current limit. Deriving the kinetic equation from nonlinear Schrödinger dynamics is also outside its claims. No assertion of historical priority is made.

Maintained by veridiscoverLab.
