import Resonance.CrossRowMass
import Resonance.ScheffeRows

/-! L1 continuity of the full incoming--outgoing row.  The row mass is
the actual fixed-output collision readout; the moving singularity is
handled by a minimum with the fixed row, not a false common majorant. -/
open MeasureTheory Set Filter Real
open scoped ENNReal Topology
namespace Resonance.CrossRowL1
noncomputable section
open ResonantMeasure CrossRowPointwise CrossDensityContinuity CrossRowMass

theorem planeRow_L1_continuousWithinAt {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q)
    {k : E} (hk : k ∈ cube R) :
    Tendsto (fun a : E => ∫ p : E, ‖planeRow R Φ a p-planeRow R Φ k p‖)
      (nhdsWithin k (cube R)) (𝓝 0) := by
  apply ScheffeRows.tendsto_integral_norm_sub
      (planeRow R Φ) (planeRow R Φ k)
      (planeRow_integrable hR Φ hΦ hpos) (planeRow_integrable hR Φ hΦ hpos k)
      (fun a => ae_of_all _ (planeRow_nonnegative hpos a))
      (ae_of_all _ (planeRow_nonnegative hpos k))
  · exact planeRow_continuousWithinAt_ae hR Φ hΦ hk
  · exact planeRow_mass_continuousOn hR Φ hΦ hpos k hk

theorem actual_cross_row_integrable {R : ℝ} (hR : 0 ≤ R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) (k : E) :
    Integrable (fun p : E =>
      (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (k,p)).toReal) := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := actual_weight_extension hθ
  have hrow (p : E) :
      (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (k,p)).toReal =
        planeRow R Φ k p := by
    rw [density_congr_on_flags R _ _ he, density_toReal_planeRow hR Φ hΦ hpos]
  simp_rw [hrow]
  exact planeRow_integrable hR Φ hΦ hpos k

theorem actual_cross_row_L1_continuousWithinAt {R : ℝ} (hR : 0 ≤ R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    {k : E} (hk : k ∈ cube R) :
    Tendsto (fun a : E => ∫ p : E,
      ‖(CrossPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal-
        (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (k,p)).toReal‖)
      (nhdsWithin k (cube R)) (𝓝 0) := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := actual_weight_extension hθ
  have hrow (a p : E) :
      (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal =
        planeRow R Φ a p := by
    rw [density_congr_on_flags R _ _ he, density_toReal_planeRow hR Φ hΦ hpos]
  simp_rw [hrow]
  exact planeRow_L1_continuousWithinAt hR Φ hΦ hpos hk

end
end Resonance.CrossRowL1
