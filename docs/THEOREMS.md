# Verified theorem catalogue

This catalogue describes the frozen release containing **690 mathematical modules and 4,992 explicit theorem declarations**. It records the mathematical content of selected final declarations, including their hypotheses and normalizations. All declaration names below are in the `Resonance` namespace.

The release was rebuilt from clean project sources with Lean 4.29.0 and mathlib revision `8a178386ffc0f5fef0b77738bb5449d50efeea95`. The imported declarations were replayed together from an initially empty Lean kernel. The audited proof dependencies contain no `unsafe` or `partial` dependencies and use only `propext`, `Classical.choice`, and `Quot.sound`. This is a replay using the same Lean kernel, not certification by a second proof assistant.

The [mathematical overview](MATHEMATICAL_OVERVIEW.md) explains the proof mechanisms and how the two collision models are kept distinct.

## 1. Pinned-chain collision invariants

Fix

$$
0<d<\frac12,\qquad \mathbb T=\mathbb R/(2\pi\mathbb Z),\qquad
\omega_d(x)=\sqrt{1-2d\cos x}.
$$

The one-particle Hilbert space uses probability Haar measure
$dm=dx/(2\pi)$. A quartet is described by three circle coordinates, with
$w=x+y-z$ in $\mathbb T$. On real lifts, set

$$
F_d(x,y,z)=\omega_d(x)+\omega_d(y)-\omega_d(z)-\omega_d(x+y-z).
$$

The resonance measure $\Xi_d$ is defined by the Euclidean-normalized surface measure
$d\mathcal H_E^2/((2\pi)^3\|\nabla F_d\|)$ on
$\{F_d=0,\ \nabla F_d\ne0\}$, restricted to a fundamental cell and pushed to the circle. It is not silently rescaled to probability measure. The normalization and quotient maps are explicit in [PinnedMeasureNormalization.lean](../Resonance/PinnedMeasureNormalization.lean).

Let $\varphi:\mathbb T\to\mathbb C$ be almost-everywhere measurable for $m$, with finite values, and suppose

$$
\varphi(x)+\varphi(y)=\varphi(z)+\varphi(w)
\quad\text{for }\Xi_d\text{-almost every quartet}.
$$

Then there is a **unique** pair $(A,B)\in\mathbb C^2$ such that

$$
\varphi=A+B\omega_d\qquad m\text{-almost everywhere}.
$$

There is also a unique smooth, $2\pi$-periodic function on $\mathbb R$ agreeing almost everywhere with the periodic lift of $\varphi$. No integrability or differentiability of $\varphi$ is assumed. The real-valued theorem gives real coefficients. Conversely, every displayed affine function of $\omega_d$ satisfies the four-term identity on **every** energy-resonant real quartet, including trivial and critical quartets. Momentum is interpreted periodically throughout, so no Umklapp branch is removed.

Final declarations in [PinnedClassificationFinal.lean](../Resonance/PinnedClassificationFinal.lean):

- `PinnedClassificationFinal.euclidean_coarea_classification_unique`
- `PinnedClassificationFinal.euclidean_coarea_unique_smooth_representative`
- `PinnedClassificationFinal.euclidean_coarea_classification_real`
- `PinnedClassificationFinal.affine_representative_all_resonances`
- `PinnedClassificationFinal.affine_representative_euclidean_invariant`

The parameter is fixed in the stated open interval. These declarations do not assert estimates uniform as $d$ approaches either endpoint.

## 2. Spectral gap for the full pinned resonance form

For a continuous weight $a:\mathbb T^4\to(0,\infty)$, define the extended nonnegative energy

$$
\mathcal D_{d,a}(f)
=\int a(x,y,z,w)\,
  |f(x)+f(y)-f(z)-f(w)|^2\,d\Xi_d
\in[0,\infty].
$$

Let $P_d$ be the orthogonal projection in $L^2(\mathbb T,m;\mathbb C)$ onto
$\operatorname{span}_{\mathbb C}\{1,\omega_d\}$. There exists
$\lambda_{d,a}>0$ such that every $f\in L^2(m;\mathbb C)$ satisfies

$$
\lambda_{d,a}\|f-P_df\|_{L^2(m)}^2\le\mathcal D_{d,a}(f).
$$

The conclusion includes functions of infinite energy. It does not require each individual term of the four-term difference to lie in the resonance-space $L^2$. No permutation symmetry of $a$ is required.

A uniform lower-weight version proves that one can choose $\lambda_d>0$ such that $a\ge b>0$ gives the lower bound $b\lambda_d$. Compactness and the positive gap are established by the proof, rather than assumed.

Final declarations in [PinnedGap.lean](../Resonance/PinnedGap.lean):

- `PinnedGap.full_coarea_spectral_gap`
- `PinnedGap.uniform_lower_weight_spectral_gap`

## 3. Maximal closed form and its self-adjoint operator

Use the same $d$, $a$, $m$, and $\Xi_d$. Define the maximal difference operator

$$
\begin{aligned}
R_{d,a}f&=f(x)+f(y)-f(z)-f(w),\\
\operatorname{Dom}(R_{d,a})
&=\{f\in L^2(m;\mathbb C):R_{d,a}f\in L^2(a\,d\Xi_d;\mathbb C)\}.
\end{aligned}
$$

This operator is closed and densely defined. Its domain contains every $C^2$ circle function. For every $\gamma>0$, the form

$$
\mathfrak a_{d,a,\gamma}(u,v)
=\frac\gamma4\int a\,R_{d,a}u\,\overline{R_{d,a}v}\,d\Xi_d
$$

is a closed nonnegative form on that full maximal domain. Here the displayed convention is linear in the first argument; the source explicitly translates it to Lean's inner-product convention.

Its associated operator is

$$
A_{d,a,\gamma}=\frac\gamma4R_{d,a}^*R_{d,a},\qquad
\operatorname{Dom}(A_{d,a,\gamma})
=\{u\in\operatorname{Dom}(R_{d,a}):R_{d,a}u\in\operatorname{Dom}(R_{d,a}^*)\}.
$$

The operator is densely defined, nonnegative, and self-adjoint. Its kernel is exactly
$\operatorname{span}_{\mathbb C}\{1,\omega_d\}$, and

$$
\mathfrak a_{d,a,\gamma}(u,u)
\ge\frac\gamma4\lambda_{d,a}\|u-P_du\|_{L^2(m)}^2.
$$

Uniqueness is with respect to the variational graph of the **entire maximal form domain**. The theorem does not assert that $C^2$ functions form a core in the form norm, that they all belong to the operator domain, or that every operator agreeing on $C^2$ must coincide with this realization.

Final declarations in [PinnedOperator.lean](../Resonance/PinnedOperator.lean):

- `PinnedOperator.pinned_closed_theorem`
- `PinnedOperator.associatedOperator_domain_iff`
- `PinnedOperator.associatedOperator_unique_form_realization`
- `PinnedOperator.associatedOperator_kernel_classification`
- `PinnedOperator.associatedOperator_paper_graph_iff`
- `PinnedOperator.form_spectral_gap`

## 4. The full fifteen-dimensional Onsager tensor

This theorem concerns a different collision model. Fix $R>0$,

$$
D_R=[-R,R]^3,\qquad
\Psi(k)=(1,k_1,k_2,k_3,|k|^2),\qquad
N_\theta(k)=\frac1{\theta\cdot\Psi(k)}.
$$

The positive parameter domain consists of all $\theta\in\mathbb R^5$ whose denominator is strictly positive on the entire closed cube. There is no assumption that the momentum coefficients vanish or that $N_\theta$ is close to a constant.

All four momenta lie in $D_R$, and the full collision measure retains both constraints

$$
k_0+k_1=k_2+k_3,\qquad
|k_0|^2+|k_1|^2=|k_2|^2+|k_3|^2.
$$

Write $P_\theta$ for the **unweighted volume $L^2$** orthogonal projection onto
$\operatorname{span}\{N_\theta\Psi_A:0\le A\le4\}$, with its proved extension to the frequency-weighted space, and set $Q_\theta=I-P_\theta$. It is not being redefined as an orthogonal projection for the weighted norm.

For $i=1,2,3$ and $A=0,\ldots,4$, the fifteen drives and cells are

$$
G_{iA}=Q_\theta(2k_iN_\theta\Psi_A),\qquad
P_\theta z_{iA}=0,\qquad
\mathfrak b_\theta(z_{iA},v)=\int_{D_R}G_{iA}v\,dk.
$$

The last equality holds for all tests in the frequency-weighted Hilbert space. The form is the full linearized collision form,

$$
\mathfrak b_\theta(u,v)
=\frac14\int\Bigl(\prod_{j=0}^3N_\theta(k_j)\Bigr)
\Delta(u/N_\theta)\,\Delta(v/N_\theta)\,d\Xi_R.
$$

The cells exist uniquely in the microscopic subspace. They define

$$
\mathsf K_{iA,jB}(\theta)
=\int_{D_R}G_{iA}z_{jB}\,dk
=\mathfrak b_\theta(z_{iA},z_{jB}).
$$

Thus $\mathsf K$ is a real symmetric positive semidefinite matrix. It also has an attained variational characterization through the actual cell problem. These assertions do not take an inverse or a positive matrix as additional input.

Identify a fifteen-component direction with
$(a,B,h)\in\mathbb R^3\times\mathbb R^{3\times3}\times\mathbb R^3$. Then

$$
\ker\mathsf K(\theta)
=\{(a,B,0):\operatorname{Sym}B=bI\text{ for some }b\in\mathbb R\}.
$$

Consequently, **the kernel has dimension 7 and the tensor has rank 8**. Moreover, for every compact set $\Theta$ contained in the positive parameter domain, there are constants $c_\Theta,C_\Theta>0$ such that, for all $\theta\in\Theta$ and all $(a,B,h)$,

$$
\begin{aligned}
c_\Theta\bigl(\|\operatorname{dev}\operatorname{Sym}B\|_F^2+|h|^2\bigr)
&\le (a,B,h)^T\mathsf K(\theta)(a,B,h)\\
&\le C_\Theta\bigl(\|\operatorname{dev}\operatorname{Sym}B\|_F^2+|h|^2\bigr).
\end{aligned}
$$

Here $\operatorname{dev}\operatorname{Sym}B=\tfrac12(B+B^T)-\tfrac13\operatorname{tr}(B)I$. The constants may depend on $R$ and $\Theta$.

| Content | Final declarations and source |
| --- | --- |
| Actual cells, integral formula, reciprocity | `ActualOnsagerTensor.transportCell_equation`, `transportCell_unique`, `tensor_original_integral`, `tensor_reciprocity` in [ActualOnsagerTensor.lean](../Resonance/ActualOnsagerTensor.lean) |
| Positivity and attained variational bound | `ActualOnsagerPositive.actual_tensor_positive`, `actual_tensor_variational_maximum` in [ActualOnsagerPositive.lean](../Resonance/ActualOnsagerPositive.lean) |
| Exact null directions | `ActualOnsagerNullDirections.actual_null_scalar_symmetric` in [ActualOnsagerNullDirections.lean](../Resonance/ActualOnsagerNullDirections.lean) |
| Kernel dimension and rank | `ActualOnsagerRank.actual_kernel_dimension`, `actual_tensor_rank` in [ActualOnsagerRank.lean](../Resonance/ActualOnsagerRank.lean) |
| Uniform quantitative bounds | `ActualOnsagerUniform.original_deviatoric_bounds`, `original_rank_one_bounds` in [ActualOnsagerUniform.lean](../Resonance/ActualOnsagerUniform.lean) |

The tensor convention above contains no $4\pi$ factor. The frozen evolution below uses the coefficient $c^{-1}\mathsf K$.

## 5. Frozen five-moment evolution and decay

Keep $R>0$ and a positive parameter $\theta$ fixed in time and space. Define the actual moment and flux matrices

$$
M_\theta=\int_{D_R}N_\theta^2\Psi\Psi^T\,dk,\qquad
J_{\theta,i}=\int_{D_R}2k_iN_\theta^2\Psi\Psi^T\,dk.
$$

The positive definiteness of $M_\theta$ is proved for these five functions on the cube. With the blocks of the tensor from Section 4, the equation is

$$
M_\theta\partial_t U+\sum_iJ_{\theta,i}\partial_{x_i}U
=c^{-1}\sum_{i,j}\mathsf K_{\theta,ij}\partial_{x_i}\partial_{x_j}U
\quad\text{on }(\mathbb R/(2\pi\mathbb Z))^3.
$$

For each $c>0$, every real Sobolev order $s$, and every real initial datum of order $s$, the formalization constructs a continuous forward trajectory with the prescribed initial value. It preserves reality and satisfies the displayed equation with a time derivative in order $s-2$, including the one-sided derivative at $t=0$. Negative orders refer to the Sobolev completion, not necessarily pointwise functions.

For a Fourier mode $\ell$, set $E_\theta(u)=u^*M_\theta u$. On each compact positive parameter set $\Theta$, there is $\delta_\Theta>0$ such that any solution of the original mode equation obeys

$$
E_\theta(u(t))\le
3\exp\!\left(-\delta_\Theta
\frac{c|\ell|^2}{c^2+|\ell|^2}t\right)E_\theta(u(0)).
$$

For $c\ge1$ and zero spatial mean in **all five components**, the constructed solution satisfies

$$
\|U(t)\|_{H^s_{M_\theta}}
\le\sqrt3\,e^{-a_\Theta t/c}\|U(0)\|_{H^s_{M_\theta}},
\qquad t\ge0.
$$

The norm here is precisely

$$
\|U\|_{H^s_{M_\theta}}^2
=\sum_{\ell\in\mathbb Z^3}(1+|\ell|^2)^s
\widehat U(\ell)^*M_\theta\widehat U(\ell).
$$

It is uniformly equivalent to the usual Sobolev norm on compact positive parameter sets. The zero Fourier mode has no positive decay rate; the zero-mean hypothesis is essential to the full-norm decay statement.

Final declarations:

- `ActualOriginalModeDecay.original_five_moment_mode_decay` in [ActualOriginalModeDecay.lean](../Resonance/ActualOriginalModeDecay.lean)
- `ActualRealSobolevPDE.original_real_complete_pde` and `original_real_complete_decay` in [ActualRealSobolevPDE.lean](../Resonance/ActualRealSobolevPDE.lean)
- The coefficient and norm definitions are in [ActualSobolevSpace.lean](../Resonance/ActualSobolevSpace.lean).

## Scope of this release

The results above are completed theorem families, not merely assumed ingredients. Their scope does not include a verified proof of the nonlinear wave-kinetic-to-Euler limit over an entire prescribed smooth Euler window, or the final strong first-order collision-current limit along that nonlinear evolution. The frozen-coefficient system in Section 5 is a separate, proved statement.

This release makes no claim of historical priority, no claim to derive the wave kinetic equation from nonlinear Schrödinger dynamics, and no identification of the cube model with the one-dimensional pinned-chain model.

Maintained by veridiscoverLab.
