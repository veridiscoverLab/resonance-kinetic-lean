import Resonance.UniformShiftSpace

/-! Exact relative-loss resolvent identities, with all positive shifts
and the same actual frequency. Equalities are in the original cube L∞,
so no artificial value of a zero corner denominator is required. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.ShiftRelativeAlgebra
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization LinftyMultiplication NormalizedLossSmooth UniformShiftSpace

def ratioOp {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : Op R :=
  (inverseOperator hR.le θ).comp (PositiveLossShift.multiplier hR hθ hz)

theorem ratioOp_bound {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : ‖ratioOp hR hθ hz‖≤‖inverseOperator hR.le θ‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (PositiveLossShift.multiplier_bound hR hθ hz) (norm_nonneg _)

theorem ratioOp_ae {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) (f : X R) :
    ratioOp hR hθ hz f=ᵐ[cubeVolume R] fun k=>
      f k*(referenceFrequency R k/(lossFrequency R (profile θ) k+z)) := by
  filter_upwards [inverseOperator_ae hR hθ (PositiveLossShift.multiplier hR hθ hz f),
    PositiveLossShift.multiplier_ae hR hθ hz f,LinftyPhysicalDomain.loss_positive_ae hR hθ]
    with k hi hm hn
  change ratioOp hR hθ hz f k=_ at hi
  rw [hi,hm,PositiveLossShift.fraction]
  field_simp

def lossOp {R : ℝ} (hR : 0≤R) (θ : Parameter) : Op R :=
  operatorMap R (lossRatioMap hR θ)

theorem lossOp_contDiffAt {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ContDiffAt ℝ ∞ (lossOp hR) θ :=
  (operatorMap R).contDiff.contDiffAt.comp θ (lossRatioMap_contDiffAt hR hθ)

def relativeOp {R : ℝ} (hR : 0<R) (θ : Parameter) {β : Parameter}
    (hβ : β∈positiveDomain R) {z : ℝ} (hz : 0≤z) : Op R :=
  1+(lossOp hR.le θ-lossOp hR.le β)*ratioOp hR hβ hz

theorem relativeOp_ae {R : ℝ} (hR : 0<R) {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) {z : ℝ} (hz : 0≤z) (f : X R) :
    relativeOp hR θ hβ hz f=ᵐ[cubeVolume R] fun k=>
      f k*((lossFrequency R (profile θ) k+z)/(lossFrequency R (profile β) k+z)) := by
  let r := ratioOp hR hβ hz f
  filter_upwards [Lp.coeFn_add f (lossOp hR.le θ r-lossOp hR.le β r),
    Lp.coeFn_sub (lossOp hR.le θ r) (lossOp hR.le β r),
    operatorMap_apply_ae R (lossRatioMap hR.le θ) r,
    operatorMap_apply_ae R (lossRatioMap hR.le β) r,
    lossRatioMap_ae hR.le hθ,lossRatioMap_ae hR.le hβ,ratioOp_ae hR hβ hz f,
    CornerInverseFrequency.referenceFrequency_positive_ae hR,
    LinftyPhysicalDomain.loss_positive_ae hR hβ] with k ha hs h1 h2 l1 l2 hr hp hb
  change relativeOp hR θ hβ hz f k=_ at ha
  change r k=_ at hr
  change lossOp hR.le θ r k=_ at h1
  change lossOp hR.le β r k=_ at h2
  simp only [Pi.add_apply,Pi.sub_apply] at ha hs
  rw [ha,hs,h1,h2,l1,l2,hr]
  have hd : lossFrequency R (profile β) k+z≠0 := (add_pos_of_pos_of_nonneg hb hz).ne'
  field_simp
  ring

theorem relativeOp_mul_reverse {R : ℝ} (hR : 0<R) {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    relativeOp hR θ hβ hz*relativeOp hR β hθ hz=1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [relativeOp_ae hR hθ hβ hz (relativeOp hR β hθ hz f),
    relativeOp_ae hR hβ hθ hz f,LinftyPhysicalDomain.loss_positive_ae hR hθ,
    LinftyPhysicalDomain.loss_positive_ae hR hβ] with k ho hi hθk hβk
  change relativeOp hR θ hβ hz (relativeOp hR β hθ hz f) k=f k
  rw [ho,hi]
  have h1 := (add_pos_of_pos_of_nonneg hθk hz).ne'
  have h2 := (add_pos_of_pos_of_nonneg hβk hz).ne'
  field_simp

theorem reverse_mul_ratio {R : ℝ} (hR : 0<R) {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    relativeOp hR β hθ hz*ratioOp hR hβ hz=ratioOp hR hθ hz := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [relativeOp_ae hR hβ hθ hz (ratioOp hR hβ hz f),
    ratioOp_ae hR hβ hz f,ratioOp_ae hR hθ hz f,
    LinftyPhysicalDomain.loss_positive_ae hR hβ] with k ho hi hr hb
  change relativeOp hR β hθ hz (ratioOp hR hβ hz f) k=ratioOp hR hθ hz f k
  rw [ho,hi,hr]
  have hd := (add_pos_of_pos_of_nonneg hb hz).ne'
  field_simp

theorem loss_mul_ratio {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    lossOp hR.le θ*ratioOp hR hθ hz=PositiveLossShift.multiplier hR hθ hz := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operatorMap_apply_ae R (lossRatioMap hR.le θ) (ratioOp hR hθ hz f),
    lossRatioMap_ae hR.le hθ,ratioOp_ae hR hθ hz f,
    PositiveLossShift.multiplier_ae hR hθ hz f,
    CornerInverseFrequency.referenceFrequency_positive_ae hR] with k ho hl hr hm hp
  change lossOp hR.le θ (ratioOp hR hθ hz f) k=PositiveLossShift.multiplier hR hθ hz f k
  change lossOp hR.le θ (ratioOp hR hθ hz f) k=_ at ho
  rw [ho,hl,hr,hm,PositiveLossShift.fraction]
  field_simp

end
end Resonance.ShiftRelativeAlgebra
