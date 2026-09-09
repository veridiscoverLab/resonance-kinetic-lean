# What Collisions Preserve, and How Fluids Emerge

*By veridiscoverLab · Draft · September 9, 2026*

A fluid description can remain correct even when some wave modes never relax to the local equilibrium it predicts. In the model studied in our paper, those modes retain the free transport of their initial data for the entire time interval. The macroscopic limit still holds because the proof controls how slowly relaxing modes contribute to the total error and transport.

This is one of the conclusions of [*Collision invariants of a pinned chain and macroscopic transport in truncated wave kinetics*](https://github.com/veridiscoverLab/resonance-kinetic-lean/blob/main/paper/output/pdf/resonance_kinetic_en.pdf). Another gives a complete answer to a collision-invariant problem raised in 2006. The two results concern different models, but they share a mathematical starting point: the relations imposed by a complete collision contain much more information than conservation alone might suggest. They can force regularity, compensate for singular measures, and determine which macroscopic gradients produce dissipation.

The historical problem begins with a chain of coupled oscillators, each attached to its equilibrium position by a restoring force. Such a chain is called *pinned*. In its kinetic description, waves exchange energy through interactions involving two incoming and two outgoing modes. A collision invariant is a quantity whose sum before an allowed interaction always equals its sum afterwards.

Write the four momentum angles as $x_0,x_1,x_2,x_3$. For a function $\varphi$ of momentum, define its collision difference by

$$
\Delta\varphi
=\varphi(x_0)+\varphi(x_1)-\varphi(x_2)-\varphi(x_3).
$$

A collision invariant satisfies $\Delta\varphi=0$ on the resonance set: the configurations that obey both momentum and energy conservation. Constants satisfy this relation because two modes enter and two leave. The energy of a mode also satisfies it by definition. Every additional independent invariant would supply another conserved density for the kinetic equation, changing the possible equilibria and the variables needed in a macroscopic description.

For the nearest-neighbour pinned chain, the energy is

$$
\omega_d(x)=\sqrt{1-2d\cos x},\qquad 0<d<\tfrac12,
$$

where $x$ is an angle modulo $2\pi$ and $d$ is a fixed coupling parameter. Momentum conservation is periodic: a collision can cross the boundary of a chosen interval of angles. Consequently, the coordinate $x$ itself does not supply an extra globally defined periodic invariant.

In their [2006 paper on energy transport](https://doi.org/10.1007/s10955-006-9171-2), Kenichiro Aoki, Jani Lukkarinen and Herbert Spohn asked whether constants and energy exhaust the collision invariants. Lukkarinen and Spohn subsequently [classified locally integrable invariants in the unpinned case, published in 2008](https://arxiv.org/abs/0704.1607). That result concerns the endpoint $d=1/2$, where the dispersion changes character. The strictly pinned question appears again in [Lukkarinen's 2016 account of phonon kinetic theory](https://doi.org/10.1007/978-3-319-29261-8_4).

The [2026 review by Pierre Germain, Joonhyun La and Angeliki Menegaki](https://arxiv.org/abs/2606.01358) still identifies the general pinned classification as open. It proves a partial result: the space of continuously differentiable invariants is finite-dimensional. Determining that space completely, and removing the regularity assumption, are further mathematical steps.

Our classification gives the precise answer for every fixed $0<d<1/2$:

$$
\varphi(x)=A+B\omega_d(x)
\quad\text{for almost every }x.
$$

Here $A$ and $B$ are constants. The input function need only be measurable and finite almost everywhere. Continuity, differentiability and integrability are not assumed; the proof produces a smooth representative. The collision identity is imposed almost everywhere with respect to the natural surface measure weighted by the energy constraint. This is a twenty-year-old classification question in mathematical kinetic theory, with a definite model and parameter range.

The first difficulty is that the most tempting proof step is initially illegal. One would like to differentiate the collision identity and use the resulting equations. A measurable function can be too irregular to differentiate, and assuming smoothness would leave the stated problem unanswered.

Instead, the proof uses collisions to create a smoothing operation. Fix one momentum and vary another along a family of allowed collisions. The identity expresses the value at the fixed momentum in terms of three other values. On a suitable resonance chart, those three locations vary nondegenerately: their motion can be used as a change of integration variable.

There is a necessary step before averaging. A merely measurable function need not have a finite integral. Comparing the sets on which its values are large, using the same collision relation and the nondegenerate changes of variables, first gives local bounds outside a set of measure zero. Smooth averaging is then legitimate. After changing variables, derivatives fall on a smooth kernel rather than on the original rough function. The invariant agrees almost everywhere with a smooth function on each chart, and the local representatives join around the circle.

This gives a useful way to think about regularity. The equation has not been replaced by a smoother approximation. Its exact compatibility relations force every admissible solution to have a smooth representative. Only at that point does the proof differentiate. Second- and third-order relations, together with periodic compatibility, eliminate every possibility except $A+B\omega_d$.

The same averages also help answer a harder quantitative question. Classification rules out additional *exact* invariants. A spectral gap must also rule out normalized functions that are almost invariant while staying away from the known invariant space. Exact classification alone cannot exclude a sequence whose oscillations become finer and finer.

Here the averaging defect is controlled by the full collision dissipation. A sequence with vanishing dissipation is therefore close to its smooth averages, which supply compactness. A hypothetical sequence violating the gap would have a nonzero limiting invariant orthogonal to both constants and energy. The classification excludes that limit. The paper obtains a positive gap, with constants depending on the fixed coupling and the positive collision weight; it does not require an unproved uniform bound at the degenerate endpoints of the coupling interval.

There is another obstacle before this argument becomes a well-defined operator theory. The measure on the resonance surface contains a factor inversely proportional to the gradient of the energy mismatch. Where that gradient degenerates, the measure can become singular. Estimating the four values in $\Delta\varphi$ separately would discard the cancellation needed to integrate their difference.

The cancellation is visible in an elementary calculation. In local real coordinates, take the four positions to be $z+u,z+v,z,z+u+v$. The collision difference is a mixed second difference. If $u=0$ or $v=0$, the positions coincide in pairs and the difference vanishes. More precisely, for a twice differentiable function,

$$
\Delta\varphi=-uv\,G_\varphi,
\qquad
\Delta\omega_d=-uv\,G_{\omega_d},
$$

where $G_\varphi$ averages the second derivative of $\varphi$ over the two increments. For the local example $\varphi(z)=z^2$, the difference is exactly $-2uv$. This example illustrates the cancellation; $z^2$ is not being treated as a periodic invariant.

Thus the energy mismatch and the quantity measured by dissipation share a vanishing factor. The proof retains the whole square $|\Delta\varphi|^2$ while regularizing the singular energy constraint. Estimates for the different critical configurations then show that smooth functions have finite dissipation. Together with the appropriate domain and closedness arguments, this constructs the full closed collision form and its nonnegative self-adjoint operator. The general operator representation theorem is classical; the work here establishes that the original singular collision expression actually satisfies its requirements.

The second part of the paper studies a three-dimensional wave kinetic equation. Momentum $k$ lies in a fixed cube $D=[-R,R]^3$, energy is $|k|^2$, and all four momenta in an allowed collision must stay in the cube. This model has five collision invariants: a constant, the three momentum components, and energy. Its equilibrium family consequently has five parameters:

$$
N_\theta(k)=\frac{1}{\alpha+\beta\cdot k+\gamma|k|^2},
\qquad \theta=(\alpha,\beta,\gamma).
$$

Here $\alpha,\gamma$ are scalars and $\beta$ is a three-component vector; the denominator must be strictly positive throughout $D$. These are Rayleigh–Jeans distributions. Allowing their parameters to vary with spatial position gives local equilibria, the states from which the macroscopic limit starts.

Quadratic energy makes the resonance geometry especially concrete. At fixed total momentum and energy, an incoming pair can be written as $V+r\sigma,V-r\sigma$, where $V$ is its centre, $r$ its radius, and $\sigma$ a unit vector. The outgoing pair has the same centre and radius but another direction. A collision compares the sums of a test function over these two pairs.

This turns the full dissipation, at each centre and radius, into a weighted variance of the pair sum. The cube constraints determine which directions are allowed, and the equilibrium determines their weights. The elementary identity behind this representation says that the mean squared difference of two independent copies of a random variable is twice its variance. The substantial step is preserving the original collision measure, its normalization and all four boundary constraints when making this change of variables.

For a simple example, centre the pair at zero and take the test function to be the first momentum component. The two values are $r\sigma_1$ and $-r\sigma_1$. Each varies with direction, but their sum is always zero. Estimating their variances separately would assign a positive cost to a conserved quantity. The pair sum retains their cancellation. Different pairs also overlap through the same underlying function, so compatibility across centres and radii remains essential.

The cube introduces modes that collide arbitrarily slowly. At a corner, an allowed resonant rectangle is forced into degenerate directions, and the collision frequency vanishes. Close to a corner it is small, so multiplying the collision operator by a large number never gives a uniform positive collision rate over the whole cube.

Let $c$ denote the collision strength, $t$ time and $X$ position. Since the velocity is $2k$, the equation at a corner momentum $\xi$ reduces exactly to free transport. For an initial distribution $f_0$, its solution there is

$$
f_c(t,X,\xi)=f_0(X-2\xi t,\xi).
$$

This expression does not depend on $c$. As $c$ tends to infinity, the corner value can keep disagreeing with the local equilibrium predicted by the Euler equation. The nearby slow modes also matter: the corners have zero volume, but that observation by itself gives no estimate for the surrounding layers.

The paper determines the rate at which the collision frequency degenerates. Up to fixed positive factors, at small distance $r$ from the corners it behaves like $r^2\log^2(C/r)$, with $C$ a fixed reference scale larger than $r$. The logarithm is essential at a critical inverse power: the integral of the frequency to the power $-3/2$ is finite, whereas the pure quadratic scale would give a divergent radial integral. This precise geometry provides the weights needed to solve the linearized collision equation and control nonlinear errors near the corners.

The resulting fluid limit applies to any fixed smooth positive local Rayleigh–Jeans initial profile, throughout any prescribed finite interval on which its five-moment Euler solution remains smooth and positive. The profile need not be a small perturbation of a constant state. For sufficiently large $c$, the kinetic solution exists over that entire interval and approaches the Euler equilibrium in momentum-integrated norms. The paper gives an $O(c^{-3/4})$ distribution error and an $O(c^{-1})$ macroscopic parameter error in the specified Sobolev norms. These are estimates on the given smooth interval, with constants depending on the profile and its positivity margin.

An exact entropy identity organizes this proof. At a fixed time and position, let $f$ be the actual distribution, $N$ the Rayleigh–Jeans state with the same five moments as $f$, and $\bar N$ the reference Euler equilibrium. Existence of this moment match along the kinetic solution is part of the theorem. Define

$$
\mathcal H(f\mid N)
=\int_D\left(\frac fN-1-\log\frac fN\right)\,dk.
$$

The integrand is nonnegative for positive $f,N$. It measures relative deviation, although it is not a symmetric distance. On the symmetric cube, for example, $f(k)=1+\eta k_1k_2$ and $N=1$ have identical five moments whenever $|\eta|R^2<1$. Symmetry makes the perturbation invisible to those moments, while its relative entropy is positive for $\eta\ne0$. Matching macroscopic information still leaves microscopic structure to control.

For the actual distribution and its matched equilibrium, the entropy splits exactly:

$$
\mathcal H(f\mid\bar N)
=\mathcal H(f\mid N)+\mathcal H(N\mid\bar N).
$$

The reason is short enough to state completely. Subtract the right-hand side from the left. What remains is the integral of $(f-N)(\bar N^{-1}-N^{-1})$. The difference of the two reciprocals is a linear combination of the five collision invariants, and $f-N$ has zero integral against each of them. The cross term is exactly zero.

The underlying three-point identity is standard in convex analysis. Its force here comes from choosing the intermediate equilibrium using the moments of the *actual evolving distribution*. The first term measures the microscopic departure from equilibrium; the second measures the error in the macroscopic parameters. Collisions control the former and the moment equations govern the latter. The identity makes their interaction explicit.

A further construction is needed to control the nonlinear evolution. Spatial transport moves a local equilibrium away from the equilibrium family. The proof builds a correction that cancels its leading residual while leaving all five moments unchanged. This corrector solves a nonlinear collision equation in complementary weighted and bounded-function spaces. It becomes small in the required norms as collisions strengthen, even though the initial equilibrium profile has fixed amplitude. Energy estimates control the remainder, while positive exchange with other momenta supplies bounds in the slow corner layers. Together these estimates keep the kinetic solution under control throughout the prescribed Euler interval.

The paper also identifies the first correction to Euler transport. Five equilibrium parameters can each vary in three spatial directions, giving fifteen gradient components. The Onsager tensor converts those gradients into first-order residual fluxes and measures their dissipation. Reciprocity and nonnegativity follow from the symmetric collision form. The more specific result is the tensor's exact degeneracy: its kernel has dimension seven, and its rank is eight, throughout the positive parameter domain.

These dimensions have a concrete explanation. Write $g=\nabla\alpha$, $B_{ij}=\partial_{X_i}\beta_j$ and $h=\nabla\gamma$. The three components of $g$ contribute no direct dissipation. Of the nine components of $B$, its three antisymmetric components and its one scalar component also contribute none. The five symmetric, trace-free components of $B$ and the three components of $h$ supply the eight dissipative directions. For example, the pointwise array $B=\lambda I$ gives a multiple of the energy invariant, while $B=\operatorname{diag}(1,-1,0)$ produces strictly positive dissipation. These are gradients of the equilibrium parameters; interpreting them directly as physical velocity gradients would require a further change of variables.

The rank calculation becomes simple once the collision kernel and the inverse on its complement have been established: it reduces to comparing polynomial coefficients. One can tell exactly which parts of a constitutive law require solving a collision equation, and which parts are already forced by conservation. The seven null directions do not represent seven independently undamped fluid modes. Spatial gradient compatibility and coupling through Euler transport give decay of every nonzero spatial Fourier mode in the constant-parameter five-moment system. Spatially constant perturbations remain conserved.

Finally, an exact microscopic entropy balance identifies the size of the collision current as well as its weak limit. This current is the signed, rescaled imbalance associated with each allowed four-mode interaction; its squared integral equals $c^2$ times the collision dissipation. A weak limit alone could hide unresolved oscillations carrying dissipation. The kinetic equation and entropy balance also determine the limiting quadratic norm, which rules out that loss and gives strong convergence. Applied to the actual nonlinear kinetic solution, this yields the first-order law for all five moment fluxes, with the same Onsager tensor. The convergence is integrated in time; it does not assert an immediate first-order match at the initial instant.

These results concern the mechanical-limits strand of Hilbert's sixth problem, posed in 1900: explaining how macroscopic equations emerge from microscopic laws. In their [2025 hard-sphere work](https://arxiv.org/abs/2503.01800), Yu Deng, Zaher Hani and Xiao Ma connected particle mechanics to fluid equations through Boltzmann's equation. On a separate wave route, [Deng and Hani's derivation of the wave kinetic equation](https://arxiv.org/abs/2104.11204), published in 2023, and their [long-time extension](https://arxiv.org/abs/2311.10082) establish kinetic descriptions from nonlinear Schrödinger dynamics under their respective scalings. Our macroscopic theorem starts from the specified wave kinetic equation with a fixed cube cutoff. Connecting it to spatially inhomogeneous microscopic wave dynamics remains a separate problem.

The [paper and Lean sources are available in the companion repository](https://github.com/veridiscoverLab/resonance-kinetic-lean). The pinned-chain classification, spectral gap and closed realization, the Onsager kernel and rank, and the constant-parameter five-moment decay have completed formalizations. The nonlinear Euler-interval limit and final strong-current theorem have paper proofs; their end-to-end formalization remains in progress. The repository records these distinctions and provides the verification procedure.
