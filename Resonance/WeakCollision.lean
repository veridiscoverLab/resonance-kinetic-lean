import Resonance.CollisionLinearization

/-! The complete weak collision functional on the one actual joint measure.
Its scalar directional derivative is proved by an exact cubic expansion, so
no interchange of a derivative and an unproved integrable expression is used. -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.WeakCollision
noncomputable section
open Collision CollisionLinearization ResonantMeasure PhysicalMarginal

theorem product_memLp_top {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    MemLp (fun a => f a * g a) ∞ μ := hg.mul' hf

theorem polynomial_memLp_top {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : A → Quartet) (hf : ∀ i, MemLp (fun a => f a i) ∞ μ) :
    MemLp (fun a => collisionPolynomial (f a)) ∞ μ := by
  have h123 := product_memLp_top (product_memLp_top (hf 1) (hf 2)) (hf 3)
  have h023 := product_memLp_top (product_memLp_top (hf 0) (hf 2)) (hf 3)
  have h013 := product_memLp_top (product_memLp_top (hf 0) (hf 1)) (hf 3)
  have h012 := product_memLp_top (product_memLp_top (hf 0) (hf 1)) (hf 2)
  exact ((h123.add h023).sub h013).sub h012

theorem linearCoefficient_odd_difference (f h : Quartet) :
    linearCoefficient f h = (1 / 2 : ℝ) *
      (collisionPolynomial (fun i => f i + h i) - collisionPolynomial (fun i => f i - h i)) -
      collisionPolynomial h := by
  dsimp [linearCoefficient, collisionPolynomial]
  ring

theorem linearCoefficient_memLp_top {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f h : A → Quartet) (hf : ∀ i, MemLp (fun a => f a i) ∞ μ)
    (hh : ∀ i, MemLp (fun a => h a i) ∞ μ) :
    MemLp (fun a => linearCoefficient (f a) (h a)) ∞ μ := by
  simp_rw [linearCoefficient_odd_difference]
  exact (((polynomial_memLp_top (fun a i => f a i + h a i) (fun i => (hf i).add (hh i))).sub
    (polynomial_memLp_top (fun a i => f a i - h a i) (fun i => (hf i).sub (hh i)))).const_mul _).sub
    (polynomial_memLp_top h hh)

def density (f g : E → ℝ) (k : FourMomenta) : ℝ :=
  quarterPairing (fun i => f (k i)) (fun i => g (k i))
def linearDensity (f h g : E → ℝ) (k : FourMomenta) : ℝ :=
  (1 / 4 : ℝ) * linearCoefficient (fun i => f (k i)) (fun i => h (k i)) *
    delta (fun i => g (k i))
def functional (R : ℝ) (f g : E → ℝ) : ℝ :=
  ∫ k, density f g k ∂pairingMeasure R

theorem delta_memLp_top {R : ℝ} (hR : 0 ≤ R) {g : E → ℝ}
    (hg : MemLp g ∞ (physicalMeasure R)) :
    MemLp (fun k : FourMomenta => delta (fun i => g (k i))) ∞ (pairingMeasure R) :=
  (((cube_leg_memLp hR 0 hg).add (cube_leg_memLp hR 1 hg)).sub
    (cube_leg_memLp hR 2 hg)).sub (cube_leg_memLp hR 3 hg)

theorem density_integrable {R : ℝ} (hR : 0 ≤ R) {f g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hg : MemLp g ∞ (physicalMeasure R)) :
    Integrable (density f g) (pairingMeasure R) := by
  letI := pairingMeasure_finite hR
  have hc := polynomial_memLp_top (fun k : FourMomenta => fun i => f (k i)) (fun i => cube_leg_memLp hR i hf)
  have hd := product_memLp_top (hc.const_mul (1 / 4 : ℝ)) (delta_memLp_top hR hg)
  rw [show density f g = (fun k => (1 / 4 : ℝ) * collisionPolynomial (fun i => f (k i)) *
    delta (fun i => g (k i))) from funext (fun k => signed_parent_pairing _ _)]
  exact hd.integrable (by simp : (1 : ℝ≥0∞) ≤ ∞)

theorem linearDensity_integrable {R : ℝ} (hR : 0 ≤ R) {f h g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R))
    (hg : MemLp g ∞ (physicalMeasure R)) : Integrable (linearDensity f h g) (pairingMeasure R) := by
  letI := pairingMeasure_finite hR
  have hc := linearCoefficient_memLp_top (fun k : FourMomenta => fun i => f (k i))
    (fun k : FourMomenta => fun i => h (k i))
    (fun i => cube_leg_memLp hR i hf) (fun i => cube_leg_memLp hR i hh)
  exact (product_memLp_top (hc.const_mul (1 / 4 : ℝ)) (delta_memLp_top hR hg)).integrable
    (by simp : (1 : ℝ≥0∞) ≤ ∞)

theorem density_exact_cubic (f h g : E → ℝ) (t : ℝ) (k : FourMomenta) :
    density (fun p => f p + t * h p) g k = density f g k + t * linearDensity f h g k +
      t ^ 2 * linearDensity h f g k + t ^ 3 * density h g k := by
  simp only [density, signed_parent_pairing, collisionPolynomial_exact_cubic, linearDensity]
  ring

theorem functional_exact_cubic {R : ℝ} (hR : 0 ≤ R) {f h g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R))
    (hg : MemLp g ∞ (physicalMeasure R)) (t : ℝ) :
    functional R (fun p => f p + t * h p) g = functional R f g +
      t * (∫ k, linearDensity f h g k ∂pairingMeasure R) +
      t ^ 2 * (∫ k, linearDensity h f g k ∂pairingMeasure R) + t ^ 3 * functional R h g := by
  unfold functional
  simp_rw [density_exact_cubic]
  have h0 := density_integrable hR hf hg
  have h1 := (linearDensity_integrable hR hf hh hg).const_mul t
  have h2 := (linearDensity_integrable hR hh hf hg).const_mul (t ^ 2)
  have h3 := (density_integrable hR hh hg).const_mul (t ^ 3)
  have ha := integral_add ((h0.add h1).add h2) h3
  have hb := integral_add (h0.add h1) h2
  have hc := integral_add h0 h1
  simp only [Pi.add_apply] at ha hb hc
  rw [ha, hb, hc, integral_const_mul, integral_const_mul, integral_const_mul]

theorem functional_directional_derivative {R : ℝ} (hR : 0 ≤ R) {f h g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R))
    (hg : MemLp g ∞ (physicalMeasure R)) :
    HasDerivAt (fun t : ℝ => functional R (fun p => f p + t * h p) g)
      (∫ k, linearDensity f h g k ∂pairingMeasure R) 0 := by
  have he : (fun t : ℝ => functional R (fun p => f p + t * h p) g) =
      (fun t => functional R f g + t * (∫ k, linearDensity f h g k ∂pairingMeasure R) +
        t ^ 2 * (∫ k, linearDensity h f g k ∂pairingMeasure R) + t ^ 3 * functional R h g) :=
    funext (functional_exact_cubic hR hf hh hg)
  rw [he]
  convert (((hasDerivAt_const (0 : ℝ) (functional R f g)).add
    ((hasDerivAt_id 0).mul_const (∫ k, linearDensity f h g k ∂pairingMeasure R))).add
    (((hasDerivAt_id 0).pow 2).mul_const (∫ k, linearDensity h f g k ∂pairingMeasure R))).add
    (((hasDerivAt_id 0).pow 3).mul_const (functional R h g)) using 1
  simp

def originalDensity (f g : E → ℝ) (k : FourMomenta) : ℝ :=
  collisionPolynomial (fun i => f (k i)) * g (k 0)

theorem originalDensity_integrable {R : ℝ} (hR : 0 ≤ R) {f g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hg : MemLp g ∞ (physicalMeasure R)) :
    Integrable (originalDensity f g) (pairingMeasure R) := by
  letI := pairingMeasure_finite hR
  exact (product_memLp_top
    (polynomial_memLp_top (fun k : FourMomenta => fun i => f (k i))
      (fun i => cube_leg_memLp hR i hf)) (cube_leg_memLp hR 0 hg)).integrable (by simp)

theorem density_original_orbit (f g : E → ℝ) (k : FourMomenta) :
    density f g k = (1 / 4 : ℝ) *
      (originalDensity f g k + originalDensity f g (swapIncomingK k) +
        originalDensity f g (swapPairsK k) + originalDensity f g (swapIncomingK (swapPairsK k))) := by
  simp [density, quarter_pairing_as_original_orbit, originalDensity, collisionPolynomial,
    incomingSwap, pairSwap, fourthOutput, swapIncomingK, swapPairsK]

theorem integral_reindex (R : ℝ) (S : FourMomenta → FourMomenta)
    (hS : MeasurePreserving S (pairingMeasure R) (pairingMeasure R))
    (F : FourMomenta → ℝ) (hF : Integrable F (pairingMeasure R)) :
    (∫ k, F (S k) ∂pairingMeasure R) = ∫ k, F k ∂pairingMeasure R := by
  have h := integral_map hS.measurable.aemeasurable (hS.map_eq.symm ▸ hF.aestronglyMeasurable)
  rw [hS.map_eq] at h
  exact h.symm

/-- The complete weak functional is proved equal to the original single output
row by symmetries of the same joint measure, with integrability paid first. -/
theorem functional_eq_original {R : ℝ} (hR : 0 ≤ R) {f g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hg : MemLp g ∞ (physicalMeasure R)) :
    functional R f g = ∫ k, originalDensity f g k ∂pairingMeasure R := by
  have h0 := originalDensity_integrable hR hf hg
  have h1 := (incoming_preserves_pairing R).integrable_comp_of_integrable h0
  have h2 := (pairs_preserves_pairing R).integrable_comp_of_integrable h0
  have hS := (incoming_preserves_pairing R).comp (pairs_preserves_pairing R)
  have h3 := hS.integrable_comp_of_integrable h0
  have ha := integral_add ((h0.add h1).add h2) h3
  have hb := integral_add (h0.add h1) h2
  have hc := integral_add h0 h1
  have h4 := integral_reindex R _ hS _ h0
  simp only [Pi.add_apply, Function.comp_def] at ha hb hc
  simp only [Function.comp_def] at h4
  unfold functional
  simp_rw [density_original_orbit]
  rw [integral_const_mul, ha, hb, hc,
    integral_reindex R _ (incoming_preserves_pairing R) _ h0,
    integral_reindex R _ (pairs_preserves_pairing R) _ h0, h4]
  ring

theorem profile_memLp_top {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    MemLp (WeightedJointMeasure.profile θ) ∞ (physicalMeasure R) := by
  obtain ⟨B, _, hb⟩ := WeightedJointMeasure.profile_bounded hθ
  apply memLp_top_of_bound (WeightedJointMeasure.profile_measurable θ).aestronglyMeasurable B
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  exact hb k hk

theorem divided_memLp_top (R : ℝ) (θ : Thermodynamics.Parameter) {f : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) :
    MemLp (fun k => f k / WeightedJointMeasure.profile θ k) ∞ (physicalMeasure R) := by
  have h := product_memLp_top hf (WeightedPhysicalForm.reciprocalProfile_memLp_top R θ)
  simpa only [WeightedPhysicalForm.reciprocalProfile_eq_inv, div_eq_mul_inv] using h

theorem rj_linearized_form_identity {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (u v : E → ℝ) :
    (∫ k, linearDensity (WeightedJointMeasure.profile θ)
      (fun p => WeightedJointMeasure.profile θ p * u p)
      (fun p => v p / WeightedJointMeasure.profile θ p) k ∂pairingMeasure R) =
      -WeightedPhysicalForm.form R θ u v := by
  unfold WeightedPhysicalForm.form WeightedJointMeasure.jointMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (WeightedJointMeasure.weight_measurable θ)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R),
    rj_reciprocal_relation_ae R θ] with k hk heq
  have hN (i : Fin 4) : 0 < WeightedJointMeasure.profile θ (k i) :=
    WeightedJointMeasure.profile_pos hθ (hk.1 i)
  have hp : 0 ≤ ∏ i : Fin 4, WeightedJointMeasure.profile θ (k i) :=
    Finset.prod_nonneg (fun i _ => (hN i).le)
  simp only [linearDensity, equilibrium_linearization _ _ (fun i => (hN i).ne') heq,
    WeightedJointMeasure.weight, ENNReal.toReal_ofReal hp, smul_eq_mul,
    WeightedPhysicalForm.weightedDifference, completeDifference, delta]
  simp [mobility, Fin.prod_univ_succ]
  ring

/-- The same original weak collision row has the exact negative RJ form as its
directional derivative, for arbitrary physically bounded perturbations/tests. -/
theorem rj_original_weak_derivative {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) {u v : E → ℝ}
    (hu : MemLp u ∞ (physicalMeasure R)) (hv : MemLp v ∞ (physicalMeasure R)) :
    HasDerivAt (fun t : ℝ => ∫ k, originalDensity
      (fun p => WeightedJointMeasure.profile θ p + t * (WeightedJointMeasure.profile θ p * u p))
      (fun p => v p / WeightedJointMeasure.profile θ p) k ∂pairingMeasure R)
      (-WeightedPhysicalForm.form R θ u v) 0 := by
  have hN := profile_memLp_top hθ
  have hNu := product_memLp_top hN hu
  have hvN := divided_memLp_top R θ hv
  have hd := functional_directional_derivative hR hN hNu hvN
  rw [rj_linearized_form_identity hθ] at hd
  have he : (fun t : ℝ => functional R
      (fun p => WeightedJointMeasure.profile θ p + t * (WeightedJointMeasure.profile θ p * u p))
      (fun p => v p / WeightedJointMeasure.profile θ p)) =
      (fun t : ℝ => ∫ k, originalDensity
        (fun p => WeightedJointMeasure.profile θ p + t * (WeightedJointMeasure.profile θ p * u p))
        (fun p => v p / WeightedJointMeasure.profile θ p) k ∂pairingMeasure R) := by
    funext t
    exact functional_eq_original hR (hN.add (hNu.const_mul t)) hvN
  rwa [he] at hd

end
end Resonance.WeakCollision
