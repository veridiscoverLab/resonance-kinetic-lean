import Resonance.WeightedOperator
import Resonance.PhysicalBalance

/-! Identification of the actual normalized derivative
`-N⁻¹ D C(N)[Nu]` with the complete RJ form operator on physical L².
The original row, all quartet reindexings, and the integral normalization are
preserved. Derivatives of the nonlinear output are taken in physical L². -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.ActualLinearization
noncomputable section
open Collision CollisionLinearization ResonantMeasure PhysicalMarginal
open PhysicalCollisionForm WeakCollision PhysicalNonlinear

def originalLinearDensity (f h g : E → ℝ) (k : FourMomenta) : ℝ :=
  linearCoefficient (fun i => f (k i)) (fun i => h (k i)) * g (k 0)

theorem originalLinearDensity_integrable {R : ℝ} (hR : 0 ≤ R) {f h g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R))
    (hg : MemLp g 2 (physicalMeasure R)) :
    Integrable (originalLinearDensity f h g) (pairingMeasure R) :=
  (joint_linear_memLp hR hf hh).integrable_mul (cube_leg_memLp hR 0 hg)

theorem linearDensity_original_orbit (f h g : E → ℝ) (k : FourMomenta) :
    linearDensity f h g k = (1 / 4 : ℝ) *
      (originalLinearDensity f h g k + originalLinearDensity f h g (swapIncomingK k) +
        originalLinearDensity f h g (swapPairsK k) +
        originalLinearDensity f h g (swapIncomingK (swapPairsK k))) := by
  simp only [linearDensity, originalLinearDensity, linearCoefficient,
    delta, swapIncomingK, swapPairsK]
  simp
  ring

theorem linear_full_eq_original {R : ℝ} (hR : 0 ≤ R) {f h g : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R))
    (hg : MemLp g 2 (physicalMeasure R)) :
    (∫ k, linearDensity f h g k ∂pairingMeasure R) =
      ∫ k, originalLinearDensity f h g k ∂pairingMeasure R := by
  have h0 := originalLinearDensity_integrable hR hf hh hg
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
  simp_rw [linearDensity_original_orbit]
  rw [integral_const_mul, ha, hb, hc,
    integral_reindex R _ (incoming_preserves_pairing R) _ h0,
    integral_reindex R _ (pairs_preserves_pairing R) _ h0, h4]
  ring

theorem divide_pairing (R : ℝ) (θ : Thermodynamics.Parameter) (f g : H R) :
    inner ℝ f (WeightedOperator.divide R θ g) = inner ℝ (WeightedOperator.divide R θ f) g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [WeightedOperator.divide_ae R θ f, WeightedOperator.divide_ae R θ g] with k hf hg
  rw [hf, hg]
  change (g k / WeightedJointMeasure.profile θ k) * f k =
    g k * (f k / WeightedJointMeasure.profile θ k)
  ring

theorem divided_linearOutput_pairing {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (u v : H R)
    (hu : MemLp u ∞ (physicalMeasure R)) :
    inner ℝ v (WeightedOperator.divide R θ
      (linearOutput hR (WeightedJointMeasure.profile θ)
        (fun p => WeightedJointMeasure.profile θ p * u p)
        (profile_memLp_top hθ) (product_memLp_top (profile_memLp_top hθ) hu))) =
      -WeightedPhysicalForm.form R θ u v := by
  rw [divide_pairing, linearOutput_pairing]
  have he : (∫ k, linearCoefficient (fun i => WeightedJointMeasure.profile θ (k i))
      (fun i => WeightedJointMeasure.profile θ (k i) * u (k i)) *
      WeightedOperator.divide R θ v (k 0) ∂pairingMeasure R) =
      ∫ k, originalLinearDensity (WeightedJointMeasure.profile θ)
        (fun p => WeightedJointMeasure.profile θ p * u p)
        (fun p => v p / WeightedJointMeasure.profile θ p) k ∂pairingMeasure R := by
    apply integral_congr_ae
    filter_upwards [(JointMultiplier.leg_quasiMeasurePreserving_cube R 0).ae_eq
      (WeightedOperator.divide_ae R θ v)] with k hk
    simp only [Function.comp_def] at hk
    simp only [originalLinearDensity, hk]
  rw [he, ← linear_full_eq_original hR (profile_memLp_top hθ)
    (product_memLp_top (profile_memLp_top hθ) hu)
    (WeightedPhysicalForm.divide_profile_memLp R θ (Lp.memLp v))]
  exact rj_linearized_form_identity hθ u v

/-- The bounded form operator agrees with the actual normalized collision
derivative for every physically bounded L² direction. -/
theorem operator_eq_actual_derivative {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (u : H R)
    (hu : MemLp u ∞ (physicalMeasure R)) :
    WeightedOperator.operator hR hθ u =
      -WeightedOperator.divide R θ
        (linearOutput hR (WeightedJointMeasure.profile θ)
          (fun p => WeightedJointMeasure.profile θ p * u p)
          (profile_memLp_top hθ) (product_memLp_top (profile_memLp_top hθ) hu)) := by
  apply ext_inner_left ℝ
  intro v
  rw [WeightedOperator.operator_form, inner_neg_right, divided_linearOutput_pairing hR hθ u v hu,
    neg_neg]
  exact WeightedPhysicalForm.form_symmetric R θ v u

theorem normalized_output_directional_derivative {R : ℝ} (hR : 0 ≤ R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (u : H R) (hu : MemLp u ∞ (physicalMeasure R)) :
    HasDerivAt (fun t : ℝ => WeightedOperator.divide R θ
      (output hR
        (fun p => WeightedJointMeasure.profile θ p + t * (WeightedJointMeasure.profile θ p * u p))
        ((profile_memLp_top hθ).add
          ((product_memLp_top (profile_memLp_top hθ) hu).const_mul t))))
      (-WeightedOperator.operator hR hθ u) 0 := by
  have hd := output_directional_derivative hR (WeightedJointMeasure.profile θ)
    (fun p => WeightedJointMeasure.profile θ p * u p)
    (profile_memLp_top hθ) (product_memLp_top (profile_memLp_top hθ) hu)
  have hn := (WeightedOperator.divide R θ).hasFDerivAt.comp_hasDerivAt 0 hd
  have he := operator_eq_actual_derivative hR hθ u hu
  rw [he, neg_neg]
  exact hn

end
end Resonance.ActualLinearization
