import Resonance.IncomingRowGeometry
import Resonance.CrossDensityContinuity

open MeasureTheory Set Filter Real Metric
open scoped ENNReal Topology
namespace Resonance.IncomingRowPointwise
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure IncomingPairMarginal IncomingRowGeometry FiberContinuity

def sphereIntegral (R : ℝ) (Φ : FourMomenta → ℝ) (k p : E) : ℝ :=
  ∫ σ, CoareaNormalization.sharpReadout R Φ (incomingQuartet ((k,p),σ)) ∂surface

def sphereRow (R : ℝ) (Φ : FourMomenta → ℝ) (k p : E) : ℝ :=
  (‖k-p‖/8)*sphereIntegral R Φ k p

theorem incomingSharp_bound {R B : ℝ} (hB : 0 ≤ B) (Φ : FourMomenta → ℝ)
    (hΦ : ∀ q ∈ CoareaNormalization.allFourFlags R, ‖Φ q‖ ≤ B) (k p : E) (σ : Sphere) :
    ‖CoareaNormalization.sharpReadout R Φ (incomingQuartet ((k,p),σ))‖ ≤ B := by
  by_cases hq : incomingQuartet ((k,p),σ) ∈ CoareaNormalization.allFourFlags R
  · rw [CoareaNormalization.sharpReadout, Set.indicator_of_mem hq]
    exact hΦ _ hq
  · rw [CoareaNormalization.sharpReadout, Set.indicator_of_notMem hq, norm_zero]
    exact hB

theorem incomingSharp_integrable {R : ℝ} (hR : 0 ≤ R) (Φ : FourMomenta → ℝ)
    (hΦ : Continuous Φ) (k p : E) :
    Integrable (fun σ => CoareaNormalization.sharpReadout R Φ (incomingQuartet ((k,p),σ))) surface := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  apply (integrable_const B).mono'
    ((CoareaNormalization.sharpReadout_measurable R hΦ.measurable).comp
      (incomingQuartet_measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  exact ae_of_all _ (incomingSharp_bound hB Φ hbound k p)

theorem sphereRow_nonnegative {R : ℝ} {Φ : FourMomenta → ℝ}
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k p : E) :
    0 ≤ sphereRow R Φ k p :=
  mul_nonneg (by positivity) (integral_nonneg (fun _ => CrossDensityContinuity.sharp_nonnegative hpos _))

theorem density_eq_ofReal_sphereRow {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k p : E) :
    IncomingPairDensity.density R (fun q => ENNReal.ofReal (Φ q)) (k,p) =
      ENNReal.ofReal (sphereRow R Φ k p) := by
  unfold IncomingPairDensity.density
  simp_rw [CrossDensityContinuity.sharp_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (incomingSharp_integrable hR Φ hΦ k p)
    (ae_of_all _ (fun _ => CrossDensityContinuity.sharp_nonnegative hpos _)),
    ← ENNReal.ofReal_mul (by positivity)]
  rfl

theorem density_toReal_sphereRow {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k p : E) :
    (IncomingPairDensity.density R (fun q => ENNReal.ofReal (Φ q)) (k,p)).toReal =
      sphereRow R Φ k p := by
  rw [density_eq_ofReal_sphereRow hR Φ hΦ hpos, ENNReal.toReal_ofReal (sphereRow_nonnegative hpos k p)]

theorem sphereIntegral_continuousWithinAt {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) {k p : E} (hk : k ∈ cube R) (hkp : k ≠ p) :
    ContinuousWithinAt (fun a : E => sphereIntegral R Φ a p) (cube R) k := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  change Tendsto _ (nhdsWithin k (cube R)) _
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Sphere => B)
  · exact Eventually.of_forall (fun a =>
      ((CoareaNormalization.sharpReadout_measurable R hΦ.measurable).comp
        (incomingQuartet_measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (incomingSharp_bound hB Φ hbound a p))
  · exact integrable_const B
  · filter_upwards [incoming_outgoing_faces_avoided hkp R] with σ hσ
    exact (incomingSharp_continuousWithinAt R Φ hΦ hk σ hσ).tendsto

theorem sphereRow_continuousWithinAt {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) {k p : E} (hk : k ∈ cube R) (hkp : k ≠ p) :
    ContinuousWithinAt (fun a : E => sphereRow R Φ a p) (cube R) k := by
  have hc : Continuous (fun a : E => ‖a-p‖/8) := by fun_prop
  exact hc.continuousWithinAt.mul (sphereIntegral_continuousWithinAt hR Φ hΦ hk hkp)

theorem sphereRow_continuousWithinAt_ae {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) {k : E} (hk : k ∈ cube R) :
    ∀ᵐ p : E ∂volume, ContinuousWithinAt (fun a : E => sphereRow R Φ a p) (cube R) k := by
  have he : ∀ᵐ p : E ∂volume, p ≠ k := by
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton k)
  filter_upwards [he] with p hp
  exact sphereRow_continuousWithinAt hR Φ hΦ hk hp.symm

theorem density_congr_on_flags (R : ℝ) (w v : FourMomenta → ℝ≥0∞)
    (hwv : ∀ q ∈ CoareaNormalization.allFourFlags R, w q=v q) (p : E×E) :
    IncomingPairDensity.density R w p = IncomingPairDensity.density R v p := by
  unfold IncomingPairDensity.density
  congr 1
  apply lintegral_congr
  intro σ
  by_cases hq : incomingQuartet (p,σ) ∈ CoareaNormalization.allFourFlags R
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    exact hwv _ hq
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

theorem actual_incoming_density_continuousWithinAt_ae {R : ℝ} (hR : 0 ≤ R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    {k : E} (hk : k ∈ cube R) :
    ∀ᵐ p : E ∂volume, ContinuousWithinAt
      (fun a : E => (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal)
      (cube R) k := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := CrossDensityContinuity.actual_weight_extension hθ
  have hrow (a p : E) : (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal =
      sphereRow R Φ a p := by
    rw [density_congr_on_flags R _ _ he, density_toReal_sphereRow hR Φ hΦ hpos]
  simp_rw [hrow]
  exact sphereRow_continuousWithinAt_ae hR Φ hΦ hk

end
end Resonance.IncomingRowPointwise
