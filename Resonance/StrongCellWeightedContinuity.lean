import Resonance.CubeLinftyMultiplier

/-! The same physical cell in its strong Y coordinate: nu_* times u
is an L-infinity vector whose operator depends continuously on theta. -/
open MeasureTheory Set
open scoped ENNReal Topology
namespace Resonance.StrongCellWeightedContinuity
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace LinftyPhysicalDomain
open StrongBoundedCell CompactParameterCell StrongCellParameterContinuity

def ratio (R : ℝ) (θ : Parameter) (k : E) : ℝ :=
  referenceFrequency R k/lossFrequency R (profile θ) k

theorem ratio_measurable (R : ℝ) (θ : Parameter) : Measurable (ratio R θ) :=
  (CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable).div
    (CollisionMarginalDensity.lossFrequency_measurable R (profile_measurable θ))

theorem ratio_memLp {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    MemLp (ratio R θ) ∞ (cubeVolume R) := by
  obtain ⟨a,ha,hb⟩ := ActualFrequencyRatio.loss_reference_lower hR hθ
  apply memLp_top_of_bound (ratio_measurable R θ).aestronglyMeasurable a⁻¹
  filter_upwards [loss_positive_ae hR hθ,CornerInverseFrequency.referenceFrequency_positive_ae hR,
    ae_restrict_mem (measurable_cube R)] with k hn hr hk
  change ‖referenceFrequency R k/lossFrequency R (profile θ) k‖≤_
  rw [Real.norm_of_nonneg (div_nonneg hr.le hn.le)]
  apply (div_le_iff₀ hn).mpr
  calc
    _ = a⁻¹*(a*referenceFrequency R k) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb k hk) (inv_nonneg.mpr ha.le)

def multiplier {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  CubeLinftyMultiplier.operator (ratio_memLp hR hθ)

theorem compact_multiplier_difference_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀(θ : Parameter)(hθ : θ∈K)(β : Parameter)(hβ : β∈K),
      ‖multiplier hR (hpos hθ)-multiplier hR (hpos hβ)‖≤C*‖θ-β‖ := by
  obtain ⟨C,hC,hb⟩ := DivideParameterContinuity.compact_inverse_loss_difference_bound hR.le hK hpos
  refine ⟨C,hC,?_⟩
  intro θ hθ β hβ
  apply CubeLinftyMultiplier.operator_difference_bound _ _ (mul_nonneg hC (norm_nonneg _))
  filter_upwards [ae_restrict_mem (measurable_cube R),
    LinftyParameterContinuity.geometricFrequency_positive_ae hR,
    CornerInverseFrequency.referenceFrequency_positive_ae hR] with k hk hg hr
  unfold ratio
  rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,norm_mul,Real.norm_of_nonneg hr.le,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hb θ hθ β hβ k hk hg) hr.le).trans_eq (by field_simp)

theorem actual_multiplier_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>multiplier hR θ.property) := by
  apply continuous_of_compact_positive
  intro K hK hpos
  obtain ⟨C,hC,hb⟩ := compact_multiplier_difference_bound hR hK hpos
  exact subtype_continuous_of_bound hC (fun x y=>hb x x.property y y.property)

def weightedCell {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (multiplier hR hθ).comp (coordinate hR hθ)

theorem weightedCell_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R)) :
    weightedCell hR hθ F=ᵐ[cubeVolume R]
      (fun k=>referenceFrequency R k*StrongBoundedCell.cell hR hθ F k) := by
  filter_upwards [CubeLinftyMultiplier.operator_ae (ratio_memLp hR hθ) (coordinate hR hθ F),
    coordinate_frequency hR hθ F,loss_positive_ae hR hθ] with k he hc hn
  change weightedCell hR hθ F k=coordinate hR hθ F k*ratio R θ k at he
  rw [he,←hc,ratio]
  field_simp

theorem actual_weightedCell_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>weightedCell hR θ.property) :=
  (actual_multiplier_continuous hR).clm_comp (actual_coordinate_continuous hR)

theorem actual_weightedCell_joint_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun z : positiveDomain R×Lp ℝ ∞ (cubeVolume R)=>weightedCell hR z.1.property z.2) :=
  ((actual_weightedCell_continuous hR).comp continuous_fst).clm_apply continuous_snd

end
end Resonance.StrongCellWeightedContinuity
