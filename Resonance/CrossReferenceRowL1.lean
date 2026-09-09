import Resonance.CrossRowWeightedBounds
import Resonance.WeightedRowLimit

/-! The actual inverse-reference-weighted plane rows are L1 continuous
on the original closed output cube.  Uniform corner tails, the compact
core lower bound, and the fixed-output row identity are all proved
geometric inputs, not hypotheses on an abstract replacement kernel. -/
open MeasureTheory Set Filter Real
open scoped ENNReal Topology
namespace Resonance.CrossReferenceRowL1
noncomputable section
set_option maxHeartbeats 900000
open ResonantMeasure CrossRowPointwise CrossDensityContinuity CrossRowMass CrossRowL1
open CrossRowWeightedBounds CollisionFrequency CornerNewtonTail CornerFrequencyBounds
open CornerInverseFrequency CollisionFrequencyCompactCore

theorem weighted_planeRow_L1_continuousWithinAt {R : ℝ} (hR : 0 < R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q)
    {k : E} (hk : k ∈ cube R) :
    Tendsto (fun a : E => ∫ p in cube R,
      inverseFrequency R p * ‖planeRow R Φ a p-planeRow R Φ k p‖)
      (nhdsWithin k (cube R)) (𝓝 0) := by
  have hi (a : E) : Integrable (planeRow R Φ a) (volume.restrict (cube R)) :=
    (planeRow_integrable hR.le Φ hΦ hpos a).mono_measure Measure.restrict_le_self
  have hL1 : Tendsto (fun a : E => ∫ p in cube R,
      ‖planeRow R Φ a p-planeRow R Φ k p‖) (nhdsWithin k (cube R)) (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun a => setIntegral_le_integral
        ((planeRow_integrable hR.le Φ hΦ hpos a).sub
          (planeRow_integrable hR.le Φ hΦ hpos k)).norm
        (ae_of_all _ (fun _ => norm_nonneg _)))
    exact planeRow_L1_continuousWithinAt hR.le Φ hΦ hpos hk
  have ht := WeightedRowLimit.weighted_L1_tendsto (cube R) self_mem_nhdsWithin
    (inverseFrequency R) (planeRow R Φ) (planeRow R Φ k)
    (inverseFrequency_nonnegative R) (planeRow_nonnegative hpos)
    (planeRow_nonnegative hpos k) hi (hi k)
    (weighted_planeRow_integrable hR Φ hΦ hpos) (weighted_planeRow_integrable hR Φ hΦ hpos k)
    hL1
  have htail : ∀ ε : ℝ, 0 < ε → ∃ T : Set E, MeasurableSet T ∧ ∃ B : ℝ, 0 < B ∧
      (∀ᵐ p ∂volume.restrict (cube R), p ∉ T → inverseFrequency R p ≤ B) ∧
      (∀ a ∈ cube R, (∫ p in T, inverseFrequency R p*planeRow R Φ a p
        ∂volume.restrict (cube R)) ≤ ε) ∧
      (∫ p in T, inverseFrequency R p*planeRow R Φ k p ∂volume.restrict (cube R)) ≤ ε := by
    intro ε hε
    obtain ⟨K,hK,hbound⟩ := weighted_planeRow_tail hR Φ hΦ hpos
    let L : ℝ := 8+K/ε
    let η : ℝ := Real.exp (-L)
    have hL8 : 8 ≤ L := by
      have hh : 0 ≤ K/ε := div_nonneg hK hε.le
      dsimp [L]
      linarith
    have hL : 0 < L := by linarith
    have hη : 0 < η := Real.exp_pos _
    have hηsmall : η ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by linarith)
    have hlog : Real.log (1/η) = L := by
      dsimp [η]
      rw [one_div,Real.log_inv,Real.log_exp,neg_neg]
    have hsmall : K/Real.log (1/η) ≤ ε := by
      rw [hlog]
      apply (div_le_iff₀ hL).mpr
      dsimp [L]
      have heq : ε*(K/ε)=K := by field_simp
      nlinarith
    obtain ⟨m,hm,hcore⟩ := referenceFrequency_compactCore_lower hR
      (show 0 < 2*R*η by positivity)
    have hsubset : fullTail R η ⊆ cube R := fun _ hp => hp.1
    have hμ : (volume.restrict (cube R)).restrict (fullTail R η) =
        volume.restrict (fullTail R η) := by
      rw [Measure.restrict_restrict (fullTail_measurable R η),inter_eq_left.mpr hsubset]
    have htbound (a : E) : (∫ p in fullTail R η, inverseFrequency R p*planeRow R Φ a p
        ∂volume.restrict (cube R)) ≤ ε := by
      rw [hμ]
      exact (hbound η hη hηsmall a).trans hsmall
    refine ⟨fullTail R η,fullTail_measurable R η,m⁻¹,inv_pos.mpr hm,?_,
      fun a _ => htbound a,htbound k⟩
    filter_upwards [ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet] with p hp
    intro hout
    have hdepth : η < cornerDepth R p := lt_of_not_ge (fun h => hout ⟨hp,h⟩)
    have hr : 2*R*η ≤ cornerRadius R p := by
      rw [cornerDepth_eq_radius_div hR] at hdepth
      have h := (le_div_iff₀ (show 0 < 2*R by positivity)).mp hdepth.le
      nlinarith
    exact inv_anti₀ hm (hcore p hp hr)
  specialize ht htail
  have heq (a p : E) :
      ‖inverseFrequency R p*planeRow R Φ a p-inverseFrequency R p*planeRow R Φ k p‖ =
        inverseFrequency R p*‖planeRow R Φ a p-planeRow R Φ k p‖ := by
    rw [← mul_sub,norm_mul,Real.norm_of_nonneg (inverseFrequency_nonnegative R p)]
  simpa only [heq] using ht

theorem actual_cross_reference_weighted_L1 {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    {k : E} (hk : k ∈ cube R) :
    Tendsto (fun a : E => ∫ p in cube R, (referenceFrequency R p)⁻¹ *
      ‖(CrossPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal-
        (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (k,p)).toReal‖)
      (nhdsWithin k (cube R)) (𝓝 0) := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := actual_weight_extension hθ
  have hrow (a p : E) : (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal =
      planeRow R Φ a p := by
    rw [density_congr_on_flags R _ _ he,density_toReal_planeRow hR.le Φ hΦ hpos]
  simp_rw [hrow]
  exact weighted_planeRow_L1_continuousWithinAt hR Φ hΦ hpos hk

end
end Resonance.CrossReferenceRowL1
