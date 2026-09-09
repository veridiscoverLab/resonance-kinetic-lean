import Resonance.SpacetimeDifference

/-! The variable-weight common measure has the exact iterated original
quartet integral. This identifies its extended nonnegative integrals before
any Bochner integral or finite-energy specialization is used. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.SpacetimeRJIntegration
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing

theorem full_lintegral {R : ℝ} (hR : 0≤R) (T : ℝ) {θ : Base→Parameter}
    (hθ : Measurable θ) (F : Joint→ℝ≥0∞) (hF : Measurable F) :
    ∫⁻p,F p∂SpacetimeRJMeasure.measure R T θ=
      ∫⁻z,∫⁻q,F (z,q)∂WeightedJointMeasure.jointMeasure R (θ z)∂baseMeasure T := by
  letI := pairingMeasure_finite hR
  rw [SpacetimeRJMeasure.measure,lintegral_withDensity_eq_lintegral_mul _
    (SpacetimeRJMeasure.weight_measurable hθ) hF]
  simp only [Pi.mul_apply]
  rw [SpacetimePairing.jointMeasure,lintegral_prod _
    ((SpacetimeRJMeasure.weight_measurable hθ).mul hF).aemeasurable]
  apply lintegral_congr
  intro z
  exact (lintegral_withDensity_eq_lintegral_mul (pairingMeasure R)
    (WeightedJointMeasure.weight_measurable (θ z))
    (show Measurable (fun q=>F (z,q)) from hF.comp measurable_prodMk_left)).symm

theorem full_lintegral_finite_iff {R : ℝ} (hR : 0≤R) (T : ℝ) {θ : Base→Parameter}
    (hθ : Measurable θ) (F : Joint→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻p,F p∂SpacetimeRJMeasure.measure R T θ)<∞ ↔
      (∫⁻z,∫⁻q,F (z,q)∂WeightedJointMeasure.jointMeasure R (θ z)∂baseMeasure T)<∞ := by
  rw [full_lintegral hR T hθ F hF]

end
end Resonance.SpacetimeRJIntegration
