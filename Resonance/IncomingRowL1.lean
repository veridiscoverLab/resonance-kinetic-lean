import Resonance.IncomingRowPointwise
import Resonance.CornerInverseFrequency

open MeasureTheory Set Filter Real Metric
open scoped ENNReal Topology
namespace Resonance.IncomingRowL1
noncomputable section
set_option maxHeartbeats 700000
open ResonantMeasure IncomingPairMarginal IncomingRowPointwise FiberContinuity

theorem sphereRow_measurable {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k : E) :
    Measurable (sphereRow R Φ k) := by
  have hm : Measurable (fun p : E =>
      (IncomingPairDensity.density R (fun q => ENNReal.ofReal (Φ q)) (k,p)).toReal) :=
    ((IncomingPairDensity.density_measurable R hΦ.measurable.ennreal_ofReal).comp
      (measurable_const.prodMk measurable_id)).ennreal_toReal
  simpa only [density_toReal_sphereRow hR Φ hΦ hpos] using hm

theorem sphereRow_uniform_bound {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ cube R, ∀ p ∈ cube R, ‖sphereRow R Φ k p‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  refine ⟨(6*R/8)*B*surface.real univ, by positivity, ?_⟩
  intro k hk p hp
  have hd : ‖k-p‖ ≤ 6*R :=
    (norm_sub_le k p).trans (by linarith [norm_le_three_R hR hk,norm_le_three_R hR hp])
  have hi : ‖sphereIntegral R Φ k p‖ ≤ B*surface.real univ :=
    norm_integral_le_of_norm_le_const (ae_of_all _ (incomingSharp_bound hB Φ hbound k p))
  rw [sphereRow,norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ ‖k-p‖/8)]
  calc
    _ ≤ (6*R/8)*(B*surface.real univ) :=
      mul_le_mul (div_le_div_of_nonneg_right hd (by norm_num)) hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem weighted_sphereRow_L1_continuousWithinAt {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q)
    (w : E → ℝ) (hwi : Integrable w (volume.restrict (cube R)))
    (hwn : 0 ≤ᵐ[volume.restrict (cube R)] w) {k : E} (hk : k ∈ cube R) :
    Tendsto (fun a : E => ∫ p in cube R, w p * ‖sphereRow R Φ a p-sphereRow R Φ k p‖)
      (nhdsWithin k (cube R)) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := sphereRow_uniform_bound hR Φ hΦ
  have ht : Tendsto (fun a : E => ∫ p in cube R,
      w p * ‖sphereRow R Φ a p-sphereRow R Φ k p‖)
      (nhdsWithin k (cube R)) (𝓝 (∫ _p in cube R, (0:ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p : E => w p*(2*C))
    · exact Eventually.of_forall (fun a => hwi.aestronglyMeasurable.mul
        (((sphereRow_measurable hR Φ hΦ hpos a).sub
          (sphereRow_measurable hR Φ hΦ hpos k)).norm.aestronglyMeasurable))
    · filter_upwards [self_mem_nhdsWithin] with a ha
      filter_upwards [hwn,ae_restrict_mem (cube_isClosed R).measurableSet] with p hw hp
      rw [norm_mul,Real.norm_of_nonneg hw,norm_norm]
      apply mul_le_mul_of_nonneg_left _ hw
      exact (norm_sub_le _ _).trans (by linarith [hbound a ha p hp,hbound k hk p hp])
    · exact hwi.mul_const (2*C)
    · have he := ae_restrict_of_ae (s := cube R) (sphereRow_continuousWithinAt_ae hR Φ hΦ hk)
      filter_upwards [he] with p hp
      have hh := (tendsto_const_nhds (x := w p)).mul
        ((hp.tendsto.sub (tendsto_const_nhds (x := sphereRow R Φ k p))).norm)
      simpa only [sub_self,norm_zero,mul_zero] using hh
  simpa only [integral_zero] using ht

theorem actual_incoming_reference_weighted_L1 {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    {k : E} (hk : k ∈ cube R) :
    Tendsto (fun a : E => ∫ p in cube R, (CollisionFrequency.referenceFrequency R p)⁻¹ *
      ‖(IncomingPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal-
        (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) (k,p)).toReal‖)
      (nhdsWithin k (cube R)) (𝓝 0) := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := CrossDensityContinuity.actual_weight_extension hθ
  have hrow (a p : E) : (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal =
      sphereRow R Φ a p := by
    rw [density_congr_on_flags R _ _ he,density_toReal_sphereRow hR.le Φ hΦ hpos]
  simp_rw [hrow]
  apply weighted_sphereRow_L1_continuousWithinAt hR.le Φ hΦ hpos
    (fun p => (CollisionFrequency.referenceFrequency R p)⁻¹)
    (CornerInverseFrequency.reference_inverse_integrable hR) _ hk
  filter_upwards [CornerInverseFrequency.referenceFrequency_positive_ae hR] with p hp
  exact inv_nonneg.mpr hp.le

end
end Resonance.IncomingRowL1
