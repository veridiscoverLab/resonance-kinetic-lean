import Mathlib

/-!
# Common four-leg collision algebra and the shared second-difference factor

The algebra below retains all four parents of one quartet.  The factor 1/4 is
explicit in the symmetrized quartet pairing.  No theorem here identifies an
abstract measure with the physical coarea measure or classifies its invariants.
The pinned factor theorem is proved from the fundamental theorem of calculus,
for every real rectangle, without assuming a factorization hypothesis.
-/

open MeasureTheory
open scoped Interval BigOperators ContDiff

namespace Resonance.Collision
noncomputable section

abbrev Quartet := Fin 4 → ℝ

/-- The full incoming-minus-outgoing difference on one common quartet. -/
def delta (h : Quartet) : ℝ := h 0 + h 1 - h 2 - h 3

/-- The original cubic collision polynomial, with its four parent terms. -/
def collisionPolynomial (f : Quartet) : ℝ :=
  f 1 * f 2 * f 3 + f 0 * f 2 * f 3 - f 0 * f 1 * f 3 - f 0 * f 1 * f 2

def mobility (f : Quartet) : ℝ := f 0 * f 1 * f 2 * f 3

/-- Four signed copies of the same collision polynomial, not independent rows. -/
def signedParents (f : Quartet) : Quartet :=
  ![collisionPolynomial f, collisionPolynomial f, -collisionPolynomial f,
    -collisionPolynomial f]

/-- The quartet-averaged weak pairing; the physical coarea symmetrization is separate. -/
def quarterPairing (f h : Quartet) : ℝ :=
  (1 / 4 : ℝ) * ∑ i : Fin 4, signedParents f i * h i

theorem signed_parent_pairing (f h : Quartet) :
    quarterPairing f h = (1 / 4 : ℝ) * collisionPolynomial f * delta h := by
  simp [quarterPairing, signedParents, Fin.sum_univ_succ, delta]
  ring

theorem collision_reciprocal_identity (f : Quartet) (hf : ∀ i, f i ≠ 0) :
    collisionPolynomial f = mobility f * delta (fun i => (f i)⁻¹) := by
  dsimp [collisionPolynomial, mobility, delta]
  field_simp [hf 0, hf 1, hf 2, hf 3]

theorem full_weak_reciprocal_identity (f h : Quartet) (hf : ∀ i, f i ≠ 0) :
    quarterPairing f h =
      (1 / 4 : ℝ) * mobility f * delta (fun i => (f i)⁻¹) * delta h := by
  rw [signed_parent_pairing, collision_reciprocal_identity f hf]
  ring

theorem invariant_quarter_pairing (f h : Quartet) (hh : delta h = 0) :
    quarterPairing f h = 0 := by
  rw [signed_parent_pairing, hh, mul_zero]

/-- Production of the logarithmic entropy, including the original factor 1/4. -/
theorem logarithmic_entropy_production (f : Quartet) (hf : ∀ i, 0 < f i) :
    quarterPairing f (fun i => (f i)⁻¹) =
      (1 / 4 : ℝ) * mobility f * (delta (fun i => (f i)⁻¹)) ^ 2 := by
  rw [full_weak_reciprocal_identity f _ (fun i => ne_of_gt (hf i))]
  ring

theorem logarithmic_entropy_production_nonneg (f : Quartet) (hf : ∀ i, 0 < f i) :
    0 ≤ quarterPairing f (fun i => (f i)⁻¹) := by
  rw [logarithmic_entropy_production f hf]
  have hm : 0 < mobility f := by
    dsimp [mobility]
    exact mul_pos (mul_pos (mul_pos (hf 0) (hf 1)) (hf 2)) (hf 3)
  positivity

/-- The negative logarithmic entropy has the opposite sign. -/
theorem negative_entropy_dissipation (f : Quartet) (hf : ∀ i, 0 < f i) :
    quarterPairing f (fun i => -(f i)⁻¹) =
      -(1 / 4 : ℝ) * mobility f * (delta (fun i => (f i)⁻¹)) ^ 2 := by
  rw [full_weak_reciprocal_identity f _ (fun i => ne_of_gt (hf i))]
  dsimp [delta]
  ring

/-- A conserved reference reciprocal profile contributes exactly zero to dissipation. -/
theorem relative_entropy_dissipation (f q : Quartet)
    (hf : ∀ i, 0 < f i) (hq : delta q = 0) :
    quarterPairing f (fun i => q i - (f i)⁻¹) =
      -(1 / 4 : ℝ) * mobility f * (delta (fun i => (f i)⁻¹)) ^ 2 := by
  rw [full_weak_reciprocal_identity f _ (fun i => ne_of_gt (hf i))]
  have hd : delta (fun i => q i - (f i)⁻¹) = -delta (fun i => (f i)⁻¹) := by
    dsimp [delta] at hq ⊢
    linarith
  rw [hd]
  ring

/-- FTC on an affine unit interval, valid also for negative or zero increments. -/
theorem affine_increment {f fp : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (fp x) x) (hp : Continuous fp) (a b : ℝ) :
    f (a + b) - f a = b * ∫ t in (0 : ℝ)..1, fp (a + t * b) := by
  have hd : ∀ t, HasDerivAt (fun t => f (a + t * b)) (fp (a + t * b) * b) t := by
    intro t
    simpa using (hf (a + t * b)).comp t (((hasDerivAt_id t).mul_const b).const_add a)
  have hc : Continuous (fun t => fp (a + t * b) * b) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ht : t ∈ Set.uIcc (0 : ℝ) 1) => hd t) (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const] at he
  simpa [mul_comm] using he.symm

/-- The actual four values occurring in the pinned critical-coordinate chart. -/
def rectangleDifference (f : ℝ → ℝ) (z u v : ℝ) : ℝ :=
  f (z + u) + f (z + v) - f z - f (z + u + v)

/-- The averaged second derivative on the same rectangle, not a factorization assumption. -/
def averagedSecond (fpp : ℝ → ℝ) (z u v : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, fpp (z + s * u + t * v)

theorem rectangle_shared_factor_of_derivatives {f fp fpp : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (fp x) x)
    (hp : ∀ x, HasDerivAt fp (fpp x) x)
    (hpp : Continuous fpp) (z u v : ℝ) :
    rectangleDifference f z u v = -u * v * averagedSecond fpp z u v := by
  have hpc : Continuous fp := continuous_iff_continuousAt.mpr
    (fun x => (hp x).continuousAt)
  have hder : ∀ x, HasDerivAt (fun x => f (x + v) - f x) (fp (x + v) - fp x) x := by
    intro x
    simpa using ((hf (x + v)).comp x ((hasDerivAt_id x).add_const v)).sub (hf x)
  have hdc : Continuous (fun x => fp (x + v) - fp x) := by fun_prop
  have hout := affine_increment hder hdc z u
  have hin (s : ℝ) : fp (z + s * u + v) - fp (z + s * u) =
      v * ∫ t in (0 : ℝ)..1, fpp (z + s * u + t * v) :=
    affine_increment hp hpp (z + s * u) v
  simp_rw [hin] at hout
  rw [intervalIntegral.integral_const_mul] at hout
  dsimp [rectangleDifference, averagedSecond]
  nlinarith [hout]

/-- The factor identity for a genuine C² function, with its actual second derivative. -/
theorem rectangle_shared_factor {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z u v : ℝ) :
    rectangleDifference f z u v =
      -u * v * averagedSecond (deriv (deriv f)) z u v := by
  have hfp : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact rectangle_shared_factor_of_derivatives
    (fun x => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x => (hfp.differentiable (by norm_num) x).hasDerivAt)
    (hfp.continuous_deriv (by norm_num)) z u v

/-- The unmodified pinned dispersion on a real lift of the circle. -/
def pinnedDispersion (d x : ℝ) : ℝ := Real.sqrt (1 - 2 * d * Real.cos x)

theorem pinned_radicand_positive {d : ℝ} (hd0 : 0 < d) (hd : d < 1 / 2) (x : ℝ) :
    0 < 1 - 2 * d * Real.cos x := by
  have hc := Real.cos_le_one x
  nlinarith

theorem pinned_dispersion_smooth {n : WithTop ℕ∞} {d : ℝ} (hd0 : 0 < d) (hd : d < 1 / 2) :
    ContDiff ℝ n (pinnedDispersion d) := by
  change ContDiff ℝ n (fun x => Real.sqrt (1 - 2 * d * Real.cos x))
  apply ContDiff.sqrt
  · fun_prop
  · intro x
    exact ne_of_gt (pinned_radicand_positive hd0 hd x)

theorem pinned_dispersion_positive {d : ℝ} (hd0 : 0 < d) (hd : d < 1 / 2) (x : ℝ) :
    0 < pinnedDispersion d x := by
  exact Real.sqrt_pos.2 (pinned_radicand_positive hd0 hd x)

/-- One and the same momentum-conserving four-leg rectangle. -/
def criticalLegs (z u v : ℝ) : Quartet := ![z + u, z + v, z, z + u + v]

theorem critical_legs_momentum (z u v : ℝ) : delta (criticalLegs z u v) = 0 := by
  simp [delta, criticalLegs]
  ring

theorem critical_legs_difference (f : ℝ → ℝ) (z u v : ℝ) :
    delta (fun i => f (criticalLegs z u v i)) = rectangleDifference f z u v := by
  rfl

/-- Both complete differences share -uv, derived by FTC on the very same quartet.
This does not assume resonance, regularity of an arbitrary measurable invariant,
or a coarea formula at a critical point. -/
theorem pinned_shared_factors {d : ℝ} (hd0 : 0 < d) (hd : d < 1 / 2)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z u v : ℝ) :
    delta (fun i => pinnedDispersion d (criticalLegs z u v i)) =
        -u * v * averagedSecond (deriv (deriv (pinnedDispersion d))) z u v ∧
    delta (fun i => f (criticalLegs z u v i)) =
        -u * v * averagedSecond (deriv (deriv f)) z u v := by
  constructor
  · rw [critical_legs_difference]
    exact rectangle_shared_factor (pinned_dispersion_smooth hd0 hd) z u v
  · rw [critical_legs_difference]
    exact rectangle_shared_factor hf z u v


/-- Three-dimensional momentum in the original Cartesian coordinates. -/
abbrev Momentum := Fin 3 → ℝ

def kineticEnergy (k : Momentum) : ℝ := ∑ j : Fin 3, k j ^ 2

def momentumDot (x y : Momentum) : ℝ := ∑ j : Fin 3, x j * y j

/-- Exactly k₀=k, k₁=k+x+y, k₂=k+x, k₃=k+y. -/
def wkeLegs (k x y : Momentum) : Fin 4 → Momentum :=
  ![k, k + x + y, k + x, k + y]

theorem wke_momentum_identity (k x y : Momentum) (j : Fin 3) :
    delta (fun i => wkeLegs k x y i j) = 0 := by
  simp [delta, wkeLegs]
  ring

/-- The factor 2 responsible for the physical delta(2 x·y)=delta(x·y)/2. -/
theorem wke_energy_identity (k x y : Momentum) :
    delta (fun i => kineticEnergy (wkeLegs k x y i)) = 2 * momentumDot x y := by
  simp [delta, wkeLegs, kineticEnergy, momentumDot, Fin.sum_univ_succ]
  ring

def reciprocalRJ (alpha : ℝ) (beta : Momentum) (gamma : ℝ) (k : Momentum) : ℝ :=
  alpha + (∑ j : Fin 3, beta j * k j) + gamma * kineticEnergy k

/-- All five collision invariants are retained in one parameterized identity. -/
theorem wke_five_invariant_identity (alpha : ℝ) (beta : Momentum) (gamma : ℝ)
    (k x y : Momentum) :
    delta (fun i => reciprocalRJ alpha beta gamma (wkeLegs k x y i)) =
      2 * gamma * momentumDot x y := by
  simp [delta, reciprocalRJ, wkeLegs, kineticEnergy, momentumDot, Fin.sum_univ_succ]
  ring

/-- All four sharp cube flags, including the output flag. -/
def allLegsInCube (R : ℝ) (k x y : Momentum) : Prop :=
  ∀ i : Fin 4, ∀ j : Fin 3, |wkeLegs k x y i j| ≤ R

/-- The genuine sharp integrand, before integration against the coarea measure. -/
def sharpCollisionIntegrand (R : ℝ) (f : Momentum → ℝ) (k x y : Momentum) : ℝ := by
  classical
  exact if allLegsInCube R k x y then collisionPolynomial (fun i => f (wkeLegs k x y i)) else 0

/-- Detailed balance for the actual reciprocal quadratic RJ profile, with all flags.
The regular coarea construction and integration are not assumed or formalized here. -/
theorem sharp_RJ_integrand_zero (R alpha : ℝ) (beta : Momentum) (gamma : ℝ)
    (hq : ∀ k : Momentum, (∀ j : Fin 3, |k j| ≤ R) →
      reciprocalRJ alpha beta gamma k ≠ 0)
    (k x y : Momentum) (hres : momentumDot x y = 0) :
    sharpCollisionIntegrand R (fun p => (reciprocalRJ alpha beta gamma p)⁻¹) k x y = 0 := by
  classical
  unfold sharpCollisionIntegrand
  split_ifs with hflags
  · rw [collision_reciprocal_identity _ (fun i => inv_ne_zero (hq _ (hflags i)))]
    have hi : delta (fun i => ((reciprocalRJ alpha beta gamma (wkeLegs k x y i))⁻¹)⁻¹) = 0 := by
      simp only [inv_inv]
      rw [wke_five_invariant_identity, hres, mul_zero]
    rw [hi, mul_zero]
  · rfl

theorem pinned_dispersion_periodic (d : ℝ) :
    Function.Periodic (pinnedDispersion d) (2 * Real.pi) := by
  intro x
  simp [pinnedDispersion, Real.cos_add_two_pi]


/-- Original quartet reindexings generating the four output parents. -/
def incomingSwap (f : Quartet) : Quartet := ![f 1, f 0, f 2, f 3]
def pairSwap (f : Quartet) : Quartet := ![f 2, f 3, f 0, f 1]
def fourthOutput (f : Quartet) : Quartet := ![f 3, f 2, f 0, f 1]

/-- The factor 1/4 is the average of four reindexed copies of the original cubic row. -/
theorem quarter_pairing_as_original_orbit (f h : Quartet) :
    quarterPairing f h = (1 / 4 : ℝ) *
      (collisionPolynomial f * h 0 +
       collisionPolynomial (incomingSwap f) * h 1 +
       collisionPolynomial (pairSwap f) * h 2 +
       collisionPolynomial (fourthOutput f) * h 3) := by
  rw [signed_parent_pairing]
  simp [delta, collisionPolynomial, incomingSwap, pairSwap, fourthOutput]
  ring

theorem negative_entropy_dissipation_nonpos (f : Quartet) (hf : ∀ i, 0 < f i) :
    quarterPairing f (fun i => -(f i)⁻¹) ≤ 0 := by
  rw [negative_entropy_dissipation f hf]
  have hm : 0 < mobility f := by
    dsimp [mobility]
    exact mul_pos (mul_pos (mul_pos (hf 0) (hf 1)) (hf 2)) (hf 3)
  have hs := sq_nonneg (delta (fun i => (f i)⁻¹))
  nlinarith [mul_nonneg (le_of_lt hm) hs]


/-! Kernel audit: full theorem types and transitive axiom dependencies. -/
#check signed_parent_pairing
#check collision_reciprocal_identity
#check full_weak_reciprocal_identity
#check invariant_quarter_pairing
#check logarithmic_entropy_production
#check logarithmic_entropy_production_nonneg
#check negative_entropy_dissipation
#check relative_entropy_dissipation
#check affine_increment
#check rectangle_shared_factor_of_derivatives
#check rectangle_shared_factor
#check pinned_radicand_positive
#check pinned_dispersion_smooth
#check pinned_dispersion_positive
#check critical_legs_momentum
#check critical_legs_difference
#check pinned_shared_factors
#check wke_momentum_identity
#check wke_energy_identity
#check wke_five_invariant_identity
#check sharp_RJ_integrand_zero
#check pinned_dispersion_periodic
#check quarter_pairing_as_original_orbit
#check negative_entropy_dissipation_nonpos

#print axioms signed_parent_pairing
#print axioms collision_reciprocal_identity
#print axioms full_weak_reciprocal_identity
#print axioms invariant_quarter_pairing
#print axioms logarithmic_entropy_production
#print axioms logarithmic_entropy_production_nonneg
#print axioms negative_entropy_dissipation
#print axioms relative_entropy_dissipation
#print axioms affine_increment
#print axioms rectangle_shared_factor_of_derivatives
#print axioms rectangle_shared_factor
#print axioms pinned_radicand_positive
#print axioms pinned_dispersion_smooth
#print axioms pinned_dispersion_positive
#print axioms critical_legs_momentum
#print axioms critical_legs_difference
#print axioms pinned_shared_factors
#print axioms wke_momentum_identity
#print axioms wke_energy_identity
#print axioms wke_five_invariant_identity
#print axioms sharp_RJ_integrand_zero
#print axioms pinned_dispersion_periodic
#print axioms quarter_pairing_as_original_orbit
#print axioms negative_entropy_dissipation_nonpos

end
end Resonance.Collision
