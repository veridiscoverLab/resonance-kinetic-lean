# Conditional proof notes

Maintained by veridiscoverLab.

These notes give ordinary mathematical derivations for several connections
needed beyond this release. They distinguish a proved implication from its
uncompleted application to the full initial-value problem. They do not add
formal verification claims to the shipped Lean snapshot. The corresponding
release requirements are listed in the [roadmap](ROADMAP.md).

## 1. Objects, normalization, and dependencies

Let

$$
 D=[-R,R]^3,\quad R>0,\qquad
 \Psi(k)=(1,k^{(1)},k^{(2)},k^{(3)},|k|^2),
 \qquad v(k)=2k.
$$

The spatial domain is the original three-dimensional torus, with its fixed
Haar volume. No normalization is changed between the kinetic equation,
entropy, and flux integrals. Write

$$
 \mathcal T=\partial_t+v\cdot\nabla_X,
 \qquad N_\theta=(\theta\cdot\Psi)^{-1}>0.
$$

Parameters lie in a fixed compact subset of the strict positive domain.
The original collision measure `dXi` retains all four sharp-cube indicators
and the constraints

$$
 k_0+k_1=k_2+k_3,\qquad
 |k_0|^2+|k_1|^2=|k_2|^2+|k_3|^2.
$$

For a function `h`, set `Delta h=h0+h1-h2-h3`. The weak normalization is

$$
 \int_D\mathcal C(f)\varphi\,dk
 =\frac14\int\Big(\prod_{i=0}^3 f_i\Big)
       \Delta(1/f)\,\Delta\varphi\,d\Xi.
$$

The collision rate is `c`: the equation is `T f=c C(f)`. Accordingly, the
Onsager tensor below has no additional `1/(4 pi)` factor.

Let `nu_*` be the original reference collision frequency and
`H_nu=L2(D,nu_* dk)`. This frequency vanishes at the corners. It is not
replaced by a positive cutoff. All later constants may depend on the fixed
cube, the positive parameter compact set, and the prescribed finite reference
window. Any additional dependence is stated where it enters.

## 2. Corrector bounds at the critical inverse-frequency exponent

### The integral estimate

Assume the original frequency has the uniform corner comparison

$$
 \nu_*(k)\asymp r(k)^2\bigl(1+\log(R/r(k))\bigr)^2,
$$

for sufficiently small distance `r(k)` to the nearest corner, and is
continuous and strictly positive away from the corners. Then

$$
 I_{3/2}:=\int_D\nu_*^{-3/2}\,dk<\infty,
 \qquad I_1:=\int_D\nu_*^{-1}\,dk<\infty.
$$

Indeed, each corner is a zero-measure point and its integral is bounded by a
constant times

$$
 \int_0^{r_0}\frac{dr}{r(1+\log(R/r))^3}<\infty.
$$

The complement is compact with frequency bounded below. The estimate must be
uniform in the direction of approach; a calculation only on a corner's
diagonal does not justify this integral.

Suppose one and the same measurable function `g` satisfies
`|g|<=A` and `nu_* |g|<=B`, with `A,B>=0`. Away from the zero-measure corners,

$$
 |g|^2\le A^{1/2}(B/\nu_*)^{3/2}.
$$

Consequently,

$$
 \|g\|_2\le I_{3/2}^{1/2}A^{1/4}B^{3/4},\qquad
 \|g\|_{H_\nu}\le I_1^{1/2}B,\qquad
 \|g\|_1\le I_1B.
$$

Thus `A=O(Lambda^(-1))` and `B=O(c^(-1))` give an unweighted
`L2` bound of order `Lambda^(-1/4)c^(-3/4)` and weighted `L2` and `L1`
bounds of order `c^(-1)`. No pointwise fast relaxation at a corner is used.

### A common corrector and its residual

The required nonlinear construction uses, for every real `s>=1`,

$$
 \|h\|_{B_s}=\|h\|_\infty+s\|\nu_*h\|_\infty.
$$

Here are the substantive inputs to that construction: a uniformly bounded
original resolvent in these norms, a nonlinear difference estimate with one
weighted input, and uniform finite-order parameter derivatives of the same
resolvent and remainder. The factor `s` multiplying the remainder is then
cancelled by the weighted input's `s^(-1)` gain. A contraction gives a unique
small branch. If two local parameter constructions overlap, uniqueness for
the same equation and five-moment constraint makes their values identical;
their derivatives then agree. This explains how local branches can form one
field, but does not supply missing derivative estimates.

With `s=c/Lambda`, fixed `Lambda>=1`, and a smooth reference `N`, the desired
corrector satisfies

$$
 \Lambda h-cN^{-1}\mathcal C(N(1+h))=-\mathcal T\log N,
 \qquad \int_D\Psi Nh\,dk=0.
$$

Put `G=Nh` and `f_app=N+G`. Direct substitution, with no asymptotic expansion,
gives

$$
 \mathcal E_{\rm app}:=\mathcal T f_{\rm app}-c\mathcal C(f_{\rm app})
 =N\{\mathcal T h+(\mathcal T\log N)h-\Lambda h\}.
$$

If the same two bounds above hold for all time-space derivatives needed on
the right, the integral estimate gives

$$
 \|\mathcal E_{\rm app}\|_{H_X^3L_k^2}
 \le C\Lambda^{3/4}c^{-3/4}.
$$

This conclusion requires the derivatives appearing in `T h`, including one
more derivative than the displayed residual norm. They cannot be inferred
from a bound on `h` alone. The corrector also creates an initial error
`f(0)-f_app(0)=-G(0)`; zero initial microscopic entropy does not remove it.

Finally, moment conservation and the zero moments of `G` yield

$$
 \int_D\Psi\mathcal E_{\rm app}\,dk
 =\sum_j\partial_j\int_D v_j\Psi G\,dk.
$$

This residual moment generally does not vanish. It belongs in the same
macroscopic equation used by the energy argument.

**Release dependency:** the nonlinear parameter derivatives, their
substitution along the reference path, and the complete residual estimates
are requirements, not consequences certified by the release.

## 3. Positive corner exchange and controlled sources

For one original quartet the cubic polynomial is

$$
 P(f)=f_1f_2f_3-f_0(f_1f_3+f_1f_2-f_2f_3).
$$

It has the exact decomposition

$$
 P(f)=f_1f_3(f_2-f_0)+f_0f_2(f_3-f_1).
$$

There is a corresponding identity with legs 2 and 3 exchanged. On an event
where the relevant adjacent leg remains in the same corner layer, the first
term is a positive two-point exchange. The second term remains a source;
discarding it would change the equation.

A partition of the original conditional quartet measure can therefore lead
to an equation of the form

$$
 \mathcal T f=c\mathcal J_f f+c\nu_b(F_b-f)+cS,
 \qquad
 \mathcal J_f h(k)=\int a_f(k,p)(h(p)-h(k))\,dp,
$$

where `a_f>=0`, `nu_b>=0`, and every omitted event is included in `S`.
This form requires the actual role partition and its integral dictionary.
It is not obtained by replacing all conditional marginals with one kernel.

### The bulk relaxation target

Suppose the equilibrium values satisfy `m<=N_i<=U<=M`, and the three bulk
inputs satisfy `|f_i|<=M` and `|f_i-N_i|<=kappa`. Define

$$
 a=f_1f_3+f_1f_2-f_2f_3,\qquad b=f_1f_2f_3,
 \qquad s_0=m^3/M.
$$

The RJ identity gives `a(N)=b(N)/N_0>=s_0`. Direct product differences give

$$
 |a-a(N)|\le6M\kappa,\qquad |b-N_0a|\le9M^2\kappa.
$$

Choose `6M kappa<=s_0/2` and `9M^2 kappa<=m s_0/4`. Then `a>=s_0/2` and

$$
 m/2\le b/a\le U+m/2\le2U.
$$

After integration over the bulk event, set `nu_b=int a` and
`F_b=(int b)/nu_b`. Its range is still `[m/2,2U]`. If `nu_b=0`, the
integrated inequalities force `int b=0`, and any value in that interval is a
valid target. The target range depends on the equilibrium bounds; the
allowed bulk error may depend on the larger temporary amplitude bound `M`.

### Comparison and the physical characteristics

At a maximum of `h` over its exchange region, `J_f h<=0`; at a minimum the
sign is reversed, and `J_f 1=0`. If a spatially constant upper barrier starts
above the data, lies above `F_b`, and has derivative at least `c sup|S|`, the
first positive maximum of `f-barrier-epsilon(t+1)` is impossible. Along the
original characteristic its derivative from the past is nonnegative, while
the equation bounds it by `-epsilon`. The lower barrier is analogous.

At a corner `xi`, the original fiber vanishes, so a continuous classical
solution retains the exact trace

$$
 f(t,X,\xi)=f(0,X-2\xi t,\xi).
$$

For a barrier based on this trace at nearby `k`, the additional transport
term is `2(k-xi) dot grad_X f(0,X-2xi t,xi)`. It must be included. Corner
reflections likewise require the original physical velocity to be
transformed consistently; they do not preserve the written transport
equation without a coordinate calculation.

### Square rows and integrated source bounds

Let `K_a` denote the nonnegative sum of the correctly identified opposite and
adjacent kernels. Assume the original rows satisfy

$$
 K_a(k,p)\le C(1+|k-p|^{-1}),\qquad
 \int_DK_a(k,p)\,dp\le C\nu_*(k).
$$

For `0<rho<=1`, integrate the squared pointwise bound in the ball of radius
`rho`. Outside that ball, use one pointwise bound and one row bound. This gives

$$
 \int_DK_a(k,p)^2dp
 \le C\{\rho+\nu_*(k)+\nu_*(k)/\rho\}.
$$

Taking `rho=sqrt(nu_*(k))` when the frequency is at most one, and adjusting
constants on its bounded remaining range, yields

$$
 \int_DK_a(k,p)^2dp\le C\sqrt{\nu_*(k)}.
$$

At zero frequency, nonnegativity and the zero row integral show that the row
vanishes almost everywhere, so the same conclusion holds.

Suppose in addition that `k -> K_a(k,.)/nu_*(.)` is continuous into `L1`,
vanishes at corners, and this assertion is uniform in the parameter compact
set. Compactness then gives

$$
 \psi(\eta):=\sup_{k\in E_\eta}\int_D
                  K_a(k,p)/\nu_*(p)\,dp\longrightarrow0.
$$

Here `E_eta` is the union of corner layers. Unweighted row continuity alone
would not imply this assertion. The bound `c||nu_*G||_infinity<=C` now gives
`c|K_aG(k)|<=C psi(eta)` there.

Write `v_eta` for the scale `eta^2(1+log(R/eta))^2`. Assume the actual
partition restricts the error input to the complement of `E_eta`, where
`nu_*(p)>=C^(-1)v_eta`, and that the output lies in `E_eta`, where
`nu_*(k)<=C v_eta`. Then Cauchy--Schwarz and the square-row bound give

$$
 \left|\int_{D\setminus E_\eta}K_a(k,p)e(p)dp\right|
 \le C v_\eta^{-1/4}\|e\|_{H_\nu}.
$$

Use the Hilbert-valued embedding
`H3_X(H_nu) -> Linfinity_X(H_nu)` before taking the time integral. If the
actual energy supplies `int_0^T ||e||_(H3_X H_nu)^2 <= C c^(-5/2)`, then

$$
 c\|S_e\|_{L_t^1L_{X,k}^\infty(E_\eta)}
 \le C_Tc^{-1/4}v_\eta^{-1/4}.
$$

When the original role estimates and RJ Lipschitz comparisons give the other
coherent sources a bound `C eta nu_*(k)`, their corresponding time cost is
`O(c eta v_eta)`. These role estimates, the corrector row limit, and the error
estimate must all concern the same partition and solution. A crude bulk
error bound multiplied by `c nu_*` cannot simply be dropped.

**Release dependency:** the complete partition, all corner transport
dictionaries, and the assembled joint source estimate remain to be connected
to the released kernel results and actual energy.

## 4. What the energy estimate would imply

Let `E` be the joint corrector-relative energy through spatial order three,
including order zero, and let `D` be its microscopic dissipation. The missing
nonlinear absorption theorem must establish, on a provisional positive
window,

$$
 E'+\gamma cD\le CE+C\Lambda^{3/2}c^{-3/2},\qquad
 E(0)\le C\Lambda^{-1/2}c^{-3/2}.
$$

This is a substantive hypothesis for the argument in this section. It is
not a restatement of Gronwall's inequality. Its proof must retain every
parent slot, moving five-moment projection, and connection term. Lower-order
dissipation is absorbed with fixed order weights. A leftover `c E` term
would prevent the required uniform conclusion.

Multiplying by `exp(-Ct)` and integrating proves

$$
 \sup_{t\le T}E(t)+c\int_0^TD(t)dt
 \le C_T(\Lambda^{-1/2}+T\Lambda^{3/2})c^{-3/2}.
$$

Fix `Lambda` before sending `c` to infinity. Choose `eta=c^(-beta)` with
`1/3<beta<1/2`. The relevant quantities satisfy

$$
 \begin{aligned}
 cv_\eta&\longrightarrow\infty,\\
 c\eta v_\eta&=O(c^{1-3\beta}(\log c)^2)\longrightarrow0,\\
 c^{-1/4}v_\eta^{-1/4}
   &=O(c^{-1/4+\beta/2}(\log c)^{-1/2})\longrightarrow0,\\
 c^{-3/4}v_\eta^{-3/4}
   &=O(c^{-3/4+3\beta/2}(\log c)^{-3/2})\longrightarrow0.
 \end{aligned}
$$

The last line is the error scale needed by the bulk amplitude estimate; its
decay does not prove that estimate. Fix the equilibrium and free-trace
bounds, temporary positive bounds, order weights, `Lambda`, bulk tolerance,
and energy threshold first. Only then choose `beta` and a sufficiently large
`c`. If the actual corner and bulk estimates strictly improve their
provisional bounds, the energy estimate improves its threshold, and the
parameter error stays strictly inside the positive neighborhood, a first
exit is impossible by continuity. At a maximal existence endpoint the
applicable amplitude continuation theorem extends the same solution. This
proves continuation to `T` once all listed improvements have been established.

The sharper macroscopic rate needs a separate equation. Set

$$
 Z_j=\int_Dv_j\Psi(f-N_{\rm matched})dk.
$$

Inverse-frequency duality, the dissipation estimate for the error, and the
corrector's weighted bound give `||Z||_(L1_t H3_X)=O(c^(-1))`. For
`a=theta_matched-theta`, the original variable-coefficient symmetric
five-moment equation then gives

$$
 \frac{d}{dt}\|a\|_{H_X^2}
 \le C\|a\|_{H_X^2}+C\|Z\|_{H_X^3},\qquad a(0)=0,
$$

provided the actual `H3` coefficient and `H2` time-derivative bounds are
available. The worst second-order commutator uses `L6` times `L3` in three
space dimensions, not an assumed fourth spatial derivative. Gronwall yields
`sup_t ||a||_(H2_X)=O(c^(-1))`. This rate does not follow from the
`c^(-3/4)` energy rate without the flux equation.

## 5. Entropy work determines the strong current

### Explicit front-end assumptions

For this conditional argument, suppose the same family of actual solutions
on `[0,T]` has fixed positive bounds for `f_c`, its matched equilibrium `N_c`,
and the prescribed smooth Euler equilibrium `N`. Assume

- `f_c -> N` strongly in physical time-space-momentum `L2`;
- `N_c -> N` in measure, with positive compact parameter bounds;
- the reciprocal fields below are bounded in `L2(time,space; H_nu)`;
- `grad_X(p_c-p) -> 0` in `L2(time,space; C(momentum))`, where
  `p_c=1/N_c` and `p=1/N`.

The intended full-window energy theorem must derive these assumptions. They
are not additional hypotheses to be silently attached to a final claim of
unconditional convergence.

Define

$$
 y_c=\frac{N}{N_c}c\left(1-\frac{N_c}{f_c}\right),
 \qquad b_c=\frac{f_cN_c}{N^2}.
$$

Then `N b_c y_c=c(f_c-N_c)` exactly. The matching coefficient `b_c` is
different from the mobility ratio `f_c/N`.

### Deriving the work limit

The microscopic relative entropy is

$$
 H_c(t)=\int_{X,D}\left(f_c/N_c-1-\log(f_c/N_c)\right).
$$

The exact five-moment match removes the actual parameter time derivative
from its balance. With local RJ initial data, `H_c(0)=0`, and the integrated
work, multiplied by `c`, is

$$
 W_c=\int b_cy_cN A_c,\qquad A_c=v\cdot\nabla_Xp_c.
$$

For `A=v dot grad_X p`, inverse-frequency integrability gives

$$
 \left\|N(A_c-A)/\sqrt{\nu_*}\right\|_2
 \le C\|\nabla_X(p_c-p)\|_{L_{t,X}^2C_k}.
$$

Consequently,

$$
 \left|W_c-\int b_cy_cNA\right|
 \le C\|y_c\|_{L_{t,X}^2H_\nu}
       \|\nabla_X(p_c-p)\|_{L_{t,X}^2C_k}\longrightarrow0.
$$

If `y_c` converges weakly along a subsequence to `u`, then `b_c y_c` has the
same weak limit. To see this, `b_c` is uniformly bounded and converges to one
in measure. For a fixed integrable density `w` and a bounded multiplier
`a_c -> 0` in measure,

$$
 \int |a_c|^2w
 \le\delta^2\int w+B^2\int_{\{|a_c|>\delta\}}w\longrightarrow0
$$

after first taking the sequence limit and then `delta -> 0`. Apply this to
each fixed Hilbert test. It does not justify strong convergence of
`(b_c-1)y_c`, whose other factor is also varying. Thus the work limit is
derived: `W_c -> int u N A`.

### The weak cell and all five constraints

Use the single common measure

$$
 d\mu_N=\Big(\prod_{i=0}^3N(k_i)\Big)d\Xi\,dt\,dX,
 \qquad R_Nh=\tfrac12\Delta(h/N).
$$

Its four leg marginals are the original frequency-weighted marginals.
Their absolute continuity transports volume convergence to the same joint
measure. Products and square roots of the four bounded mobility factors
therefore converge on fixed complete quartet tests. There is no independent
subsequence or resampling for each leg.

The original equation, tested against compactly supported smooth functions,
identifies any weak physical limit of `c C(f_c)` as `T N`: integrate the
transport derivative onto the fixed test and use the strong zero-order
convergence. The original signed collision formula then gives

$$
 \langle R_Nu,R_Nv\rangle
 =\int v(-\mathcal T N/N)
 \quad\text{for every }v\in L_{t,X}^2H_\nu.
$$

The extension to this entire space needs density and continuity. Physical
tests multiplied by `N` are dense: truncate both the function and the sets
where `nu_*` is small, approximate in the weighted norm, and use the positive
bounds for `N`. The right-hand functional is continuous by `I_1<infinity`.
These arguments are required connections, not consequences of names assigned
to an abstract operator.

Actual matching gives `int_D N b_c y_c Psi=0`. Testing in time and space and
passing to the weak limit yields `int_D N u Psi=0` almost everywhere. In
particular, `int u N p_t=0` for the given smooth parameter field. Since

$$
 -\mathcal T N/N=N(p_t+A),
$$

the cell equation with `v=u` shows

$$
 \|R_Nu\|^2=\int uN(p_t+A)=\int uNA=\lim W_c.
$$

The original five-dimensional kernel classification and weighted coercivity
give uniqueness after imposing these five constraints. This is what permits
passing from subsequences to the full sequence.

### Norm equality without discarding the endpoint

Put

$$
 m_c=\prod_{i=0}^3f_c(k_i)/N(k_i),\qquad
 J_c=\sqrt{m_c}\,R_Ny_c.
$$

The complete reciprocal difference is
`Delta(y_c/N)=-c Delta(1/f_c)`, since `1/N_c` is a collision invariant.
The original entropy balance is therefore exactly

$$
 \|J_c\|_{L^2(\mu_N)}^2+cH_c(T)=W_c.
$$

The common-multiplier argument gives `J_c` weakly convergent to `R_Nu`.
Now use `H_c(T)>=0` and weak lower semicontinuity:

$$
 \limsup\|J_c\|^2\le\|R_Nu\|^2\le\liminf\|J_c\|^2.
$$

Weak convergence plus norm convergence proves strong convergence in the
whole joint `L2` space. Only afterwards does the balance imply `cH_c(T)->0`.
This argument covers the full open time window `(0,T)` without assuming
convergence of a scaled initial trace or deleting a terminal contribution.

## 6. Recovering the kernel and the physical output

Uniform positive bounds permit removal of `sqrt(m_c)`, giving
`R_N(y_c-u)->0`. This alone controls only the quotient by the five-dimensional
kernel. Set `kappa=N Psi` and decompose

$$
 y_c-u=g_c+\kappa^Ta_c,\qquad g_c=Q_N(y_c-u),
$$

where `Q_N` is the bounded extension of the original unweighted moment
projection. It need not be orthogonal in `H_nu`. Weighted coercivity gives
`g_c->0`. The actual constraint implies

$$
 \left(\int_D b_c\kappa\kappa^Tdk\right)a_c
 =-\int_D\kappa b_cg_cdk-\int_D\kappa(b_c-1)u\,dk.
$$

The left Gram matrix is uniformly positive. The right side tends to zero by
`kappa/sqrt(nu_*) in L2`, the convergence of `g_c`, and multiplier convergence
on the fixed function `u`. Hence `y_c->u` in the full weighted space.
The exact identity `c(f_c-N_c)=N b_c y_c` then gives strong convergence to
`Nu` in `L2(time,space; H_nu)` and in `L2(time,space; L1(momentum))`.
It does not give unweighted momentum `L2` convergence.

Let `S phi=Delta phi/2`, from the original physical `L2` space to joint
`L2(mu_N)`. The actual marginal bounds make `S` bounded. The physical weak
identity, including its sign, is

$$
 c\mathcal C(f_c)=-S^*(\sqrt{m_c}J_c)
 \longrightarrow-S^*R_Nu=\mathcal T N.
$$

The convergence is strong in physical time-space-momentum `L2`. This adjoint
is not the Riesz return in the frequency-weighted source space.

For every spatial index `i` and moment index `a`, the functional
`h -> int_D v_i Psi_a N h` is continuous on `H_nu`. Thus all fifteen fluxes
converge together. If

$$
 \mathcal G_i^a=Q_N(v_iN\Psi_a),\qquad
 \mathsf K_{ij}^{ab}
 =\langle\mathcal G_i^a,L_{N,Q}^{-1}\mathcal G_j^b\rangle,
$$

the cell identity gives

$$
 cZ_{c,i}^a\longrightarrow
 \sum_{j,b}\mathsf K_{ij}^{ab}(N)\partial_j\theta_b
 \quad\text{in }L^2_{t,X}.
$$

Continuity of the original tensor on the positive parameter compact set and
the actual gradient convergence permit replacing the reference expression
by `mathsf K(N_c) grad theta_c`. The exact moment equation consequently reads

$$
 M(\theta_c)\partial_t\theta_c+
 \sum_jJ_j(\theta_c)\partial_j\theta_c
 =c^{-1}\operatorname{div}(\mathsf K(N_c)\nabla\theta_c)
   +o(c^{-1})
 \quad\text{in }L_t^2H_X^{-1}.
$$

This is a conditional derivation from the actual full-window estimates and
the displayed connections. Their final Lean composition is not shipped in
this release. The argument neither constructs a nonlinear Schrödinger flow
nor identifies a Gaussian reference history with that flow. Corner traces
can retain their exact initial free transport while these integrated and
frequency-weighted limits hold.
