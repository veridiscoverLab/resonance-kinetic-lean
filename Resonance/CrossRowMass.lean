import Resonance.FixedCrossRow
import Resonance.CrossDensityContinuity

/-! Exact finite row masses for the original sharp plane kernel.  The
identities are pointwise in the physical output, including its boundary. -/
open MeasureTheory Set Real Filter
open scoped ENNReal Topology
namespace Resonance.CrossRowMass
noncomputable section
set_option maxHeartbeats 600000
open ResonantMeasure CrossRowPointwise CrossDensityContinuity CollisionFiber FiberContinuity

theorem planeRow_measurable {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k : E) :
    Measurable (planeRow R Φ k) := by
  have hm : Measurable (fun p : E =>
      (CrossPairDensity.density R (fun q => ENNReal.ofReal (Φ q)) (k,p)).toReal) :=
    ((CrossPairDensity.density_measurable R hΦ.measurable.ennreal_ofReal).comp
      (measurable_const.prodMk measurable_id)).ennreal_toReal
  simpa only [density_toReal_planeRow hR Φ hΦ hpos] using hm

theorem continuous_fiber_integrable {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) (k : E) :
    Integrable Φ (fiberMeasure R k) := by
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  apply (integrable_const B).mono' hΦ.measurable.aestronglyMeasurable
  filter_upwards [fiber_support R k] with q hq
  exact hbound q hq.1

theorem planeRow_lintegral {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k : E) :
    (∫⁻ p : E, ENNReal.ofReal (planeRow R Φ k p)) =
      ENNReal.ofReal (fiberReadout R Φ k) := by
  have hp : 0 ≤ᵐ[ fiberMeasure R k ] Φ := by
    filter_upwards [fiber_support R k] with q hq
    exact hpos q hq.1
  rw [fiberReadout, ofReal_integral_eq_lintegral_ofReal (continuous_fiber_integrable hR Φ hΦ k) hp]
  have h := FixedCrossRow.fiber_cross_lintegral R k (fun q => ENNReal.ofReal (Φ q))
    hΦ.measurable.ennreal_ofReal
  simpa only [density_eq_ofReal_planeRow hR Φ hΦ hpos, fiberReadout] using h.symm

theorem planeRow_integrable {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k : E) :
    Integrable (planeRow R Φ k) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (planeRow_measurable hR Φ hΦ hpos k).aestronglyMeasurable
    (ae_of_all _ (planeRow_nonnegative hpos k))).mp
  rw [planeRow_lintegral hR Φ hΦ hpos]
  exact ENNReal.ofReal_ne_top

theorem planeRow_integral {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k : E) :
    (∫ p : E, planeRow R Φ k p) = fiberReadout R Φ k := by
  have hi := planeRow_integrable hR Φ hΦ hpos k
  have hp : 0 ≤ᵐ[fiberMeasure R k] Φ := by
    filter_upwards [fiber_support R k] with q hq
    exact hpos q hq.1
  have he := planeRow_lintegral hR Φ hΦ hpos k
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (planeRow_nonnegative hpos k))] at he
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (planeRow_nonnegative hpos k)) (integral_nonneg_of_ae hp)).mp he

theorem planeRow_mass_continuousOn {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) :
    ContinuousOn (fun k => ∫ p : E, planeRow R Φ k p) (cube R) := by
  simp_rw [planeRow_integral hR Φ hΦ hpos]
  exact fiberReadout_continuousOn hR Φ hΦ

end
end Resonance.CrossRowMass
