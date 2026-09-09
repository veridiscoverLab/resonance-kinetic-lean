import Resonance.StrongCellWeightedContinuity

/-! Nonnegative shifts of the original loss, on the same cube.  The
zero-shift value is one only almost everywhere, retaining all corners. -/
open MeasureTheory Set
open scoped ENNReal Topology
namespace Resonance.PositiveLossShift
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace LinftyPhysicalDomain
open StrongCellParameterContinuity CompactParameterCell

def fraction (R : ℝ) (θ : Parameter) (z : ℝ) (k : E) : ℝ :=
  lossFrequency R (profile θ) k/(lossFrequency R (profile θ) k+z)

theorem fraction_measurable (R : ℝ) (θ : Parameter) (z : ℝ) :
    Measurable (fraction R θ z) := by
  have hm := CollisionMarginalDensity.lossFrequency_measurable R (profile_measurable θ)
  exact hm.div (hm.add_const z)

theorem fraction_bounds {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) {k : E} (hk : k∈cube R) :
    0≤fraction R θ z k ∧ fraction R θ z k≤1 := by
  have hn := ActualFrequencyRatio.loss_nonnegative hR hθ hk
  unfold fraction
  refine ⟨div_nonneg hn (add_nonneg hn hz),?_⟩
  by_cases he : lossFrequency R (profile θ) k+z=0
  · rw [he,div_zero]; norm_num
  · exact (div_le_one (lt_of_le_of_ne (add_nonneg hn hz) (Ne.symm he))).mpr (le_add_of_nonneg_right hz)

theorem fraction_memLp {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    MemLp (fraction R θ z) ∞ (cubeVolume R) := by
  apply memLp_top_of_bound (fraction_measurable R θ z).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  rw [Real.norm_of_nonneg (fraction_bounds hR hθ hz hk).1]
  exact (fraction_bounds hR hθ hz hk).2

def multiplier {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  CubeLinftyMultiplier.operator (fraction_memLp hR hθ hz)

theorem multiplier_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R)) :
    multiplier hR hθ hz F=ᵐ[cubeVolume R] (fun k=>F k*fraction R θ z k) :=
  CubeLinftyMultiplier.operator_ae _ F

theorem multiplier_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : multiplier hR hθ (show (0:ℝ)≤0 from le_rfl)=1 := by
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  filter_upwards [multiplier_ae hR hθ (show (0:ℝ)≤0 from le_rfl) F,
    loss_positive_ae hR hθ] with k he hn
  change (multiplier hR hθ (show (0:ℝ)≤0 from le_rfl) F) k=F k
  rw [he,fraction,add_zero,div_self hn.ne',mul_one]

theorem multiplier_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) : ‖multiplier hR hθ hz‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  apply CubeLinftyMultiplier.vector_bound (fraction_memLp hR hθ hz) zero_le_one
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  rw [Real.norm_of_nonneg (fraction_bounds hR hθ hz hk).1]
  exact (fraction_bounds hR hθ hz hk).2

theorem compact_fraction_difference_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ∈K,∀β∈K,∀z : ℝ,0≤z →
      ∀ᵐk∂cubeVolume R,‖fraction R θ z k-fraction R β z k‖≤C*‖θ-β‖ := by
  obtain ⟨a,b,C,ha,hb,hC,hl,hd⟩ := FrequencyParameterBounds.compact_loss_difference_bound hR.le hK hpos
  refine ⟨C/a+b*C/a^2,by positivity,?_⟩
  intro θ hθ β hβ z hz
  filter_upwards [ae_restrict_mem (measurable_cube R),
    LinftyParameterContinuity.geometricFrequency_positive_ae hR] with k hk hg
  have he := NormalizedParameterAlgebra.weighted_quotient_difference ha hg hg.le
    (norm_nonneg (θ-β)) hC hb.le hC
    ((hl θ hθ k hk).1.trans (le_add_of_nonneg_right hz))
    ((hl β hβ k hk).1.trans (le_add_of_nonneg_right hz))
    (hd θ hθ β hβ k hk)
    (by rw [abs_of_nonneg (ActualFrequencyRatio.loss_nonnegative hR (hpos hβ) hk)]
        exact (hl β hβ k hk).2)
    (by simpa only [add_sub_add_right_eq_sub] using hd θ hθ β hβ k hk)
  simpa only [div_self hg.ne',mul_one,Real.norm_eq_abs] using he

theorem compact_multiplier_difference_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀(θ : Parameter)(hθ : θ∈K)(β : Parameter)(hβ : β∈K)
      (z : ℝ)(hz : 0≤z),‖multiplier hR (hpos hθ) hz-multiplier hR (hpos hβ) hz‖≤C*‖θ-β‖ := by
  obtain ⟨C,hC,hb⟩ := compact_fraction_difference_bound hR hK hpos
  exact ⟨C,hC,fun θ hθ β hβ z hz=>CubeLinftyMultiplier.operator_difference_bound _ _
    (mul_nonneg hC (norm_nonneg _)) (hb θ hθ β hβ z hz)⟩

def shiftedDivide {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Space R :=
  (divide hR hθ).comp (multiplier hR hθ hz)

theorem shiftedDivide_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R)) :
    shiftedDivide hR hθ hz F=ᵐ[cubeVolume R]
      (fun k=>F k/(lossFrequency R (profile θ) k+z)) := by
  filter_upwards [divide_ae_volume hR hθ (multiplier hR hθ hz F),
    multiplier_ae hR hθ hz F,loss_positive_ae hR hθ] with k hu hm hn
  change shiftedDivide hR hθ hz F k=(multiplier hR hθ hz F) k/lossFrequency R (profile θ) k at hu
  rw [hu,hm,fraction]
  field_simp

theorem shifted_frequency_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R)) :
    (fun k=>(lossFrequency R (profile θ) k+z)*shiftedDivide hR hθ hz F k)=ᵐ[cubeVolume R] F := by
  filter_upwards [shiftedDivide_ae hR hθ hz F,loss_positive_ae hR hθ] with k hu hn
  rw [hu,mul_div_cancel₀ _ (ne_of_gt (add_pos_of_pos_of_nonneg hn hz))]

end
end Resonance.PositiveLossShift
