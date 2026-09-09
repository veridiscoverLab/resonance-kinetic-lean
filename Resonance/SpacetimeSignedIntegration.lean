import Resonance.SpacetimeRJIntegration

/-! Signed integration on the original common weighted measure. The
actual absolute integrability hypothesis is transported to the density
integrand before Fubini; a default-zero integral cannot supply the equality. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeSignedIntegration
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing SpacetimeRJMeasure

theorem full_integral {R : ℝ} (hR : 0 ≤ R) (T : ℝ) {θ : Base → Parameter}
    (hm : Measurable θ) {F : Joint → ℝ}
    (hi : Integrable F (SpacetimeRJMeasure.measure R T θ)) :
    (∫ p, F p ∂SpacetimeRJMeasure.measure R T θ) =
      ∫ a, ∫ q, F (a,q) ∂WeightedJointMeasure.jointMeasure R (θ a) ∂baseMeasure T := by
  letI := pairingMeasure_finite hR
  have hw : ∀ᵐ p ∂SpacetimePairing.jointMeasure R T, weight θ p < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hi' := (integrable_withDensity_iff_integrable_smul' (weight_measurable hm) hw).mp hi
  rw [SpacetimeRJMeasure.measure,
    integral_withDensity_eq_integral_toReal_smul (weight_measurable hm) hw]
  rw [SpacetimePairing.jointMeasure,integral_prod _ hi']
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only
  rw [WeightedJointMeasure.jointMeasure,
    integral_withDensity_eq_integral_toReal_smul (WeightedJointMeasure.weight_measurable (θ a))
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rfl

end
end Resonance.SpacetimeSignedIntegration
