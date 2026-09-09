import Resonance.ShiftRelativeAlgebra

/-! Actual loss multipliers are smooth in all five parameters in the
common supremum norm over z in [0,1]. This does not require continuity
of the multiplier at zero as a function of z. -/
open Set
open scoped ENNReal ContDiff
namespace Resonance.UniformShiftSmooth
noncomputable section
set_option maxHeartbeats 1800000
open Thermodynamics JointWeightComparison LinftyMultiplication NormalizedLossSmooth
open UniformShiftSpace ShiftRelativeAlgebra

def actualRatioFamily {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) : Family R :=
  ofBound R (fun z=>ratioOp hR hθ z.property.1) ‖inverseOperator hR.le θ‖
    (fun z=>ratioOp_bound hR hθ z.property.1)

theorem actualRatioFamily_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    actualRatioFamily hR hθ z=ratioOp hR hθ z.property.1 := rfl

def relativeFamily {R : ℝ} (hR : 0<R) (θ : Parameter) {β : Parameter}
    (hβ : β∈positiveDomain R) : Family R :=
  1+(constMap R (lossOp hR.le θ)-constMap R (lossOp hR.le β))*actualRatioFamily hR hβ

theorem relativeFamily_apply {R : ℝ} (hR : 0<R) (θ : Parameter) {β : Parameter}
    (hβ : β∈positiveDomain R) (z : Shift) :
    relativeFamily hR θ hβ z=relativeOp hR θ hβ z.property.1 := rfl

def relativeUnit {R : ℝ} (hR : 0<R) {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) : (Family R)ˣ where
  val := relativeFamily hR θ hβ
  inv := relativeFamily hR β hθ
  val_inv := by
    apply lp.ext
    funext z
    exact relativeOp_mul_reverse hR hθ hβ z.property.1
  inv_val := by
    apply lp.ext
    funext z
    exact relativeOp_mul_reverse hR hβ hθ z.property.1

theorem relativeFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) :
    ContDiffAt ℝ ∞ (fun α=>relativeFamily hR α hβ) θ :=
  contDiffAt_const.add ((((constMap R).contDiff.contDiffAt.comp θ
    (lossOp_contDiffAt hR.le hθ)).sub contDiffAt_const).mul contDiffAt_const)

def ratioFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : Family R :=
  Ring.inverse (relativeFamily hR θ (unitParameter_positive R))*
    actualRatioFamily hR (unitParameter_positive R)

theorem ratioFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ratioFamily hR θ=actualRatioFamily hR hθ := by
  unfold ratioFamily
  have hi : Ring.inverse (relativeFamily hR θ (unitParameter_positive R))=
      relativeFamily hR unitParameter hθ :=
    Ring.inverse_unit (relativeUnit hR hθ (unitParameter_positive R))
  rw [hi]
  apply lp.ext
  funext z
  exact reverse_mul_ratio hR hθ (unitParameter_positive R) z.property.1

theorem ratioFamily_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    ratioFamily hR θ z=ratioOp hR hθ z.property.1 := by
  rw [ratioFamily_eq hR hθ]
  rfl

theorem ratioFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (ratioFamily hR) θ :=
  ((contDiffAt_ringInverse (𝕜:=ℝ) (n:=∞)
    (relativeUnit hR hθ (unitParameter_positive R))).comp θ
      (relativeFamily_contDiffAt hR hθ (unitParameter_positive R))).mul contDiffAt_const

def multiplierFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : Family R :=
  constMap R (lossOp hR.le θ)*ratioFamily hR θ

theorem multiplierFamily_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    multiplierFamily hR θ z=PositiveLossShift.multiplier hR hθ z.property.1 := by
  change lossOp hR.le θ*ratioFamily hR θ z=_
  rw [ratioFamily_apply hR hθ]
  exact loss_mul_ratio hR hθ z.property.1

theorem multiplierFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (multiplierFamily hR) θ :=
  ((constMap R).contDiff.contDiffAt.comp θ (lossOp_contDiffAt hR.le hθ)).mul
    (ratioFamily_contDiffAt hR hθ)

theorem actual_ratioFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (ratioFamily hR) (positiveDomain R) :=
  fun _ hθ=>(ratioFamily_contDiffAt hR hθ).contDiffWithinAt

theorem actual_multiplierFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (multiplierFamily hR) (positiveDomain R) :=
  fun _ hθ=>(multiplierFamily_contDiffAt hR hθ).contDiffWithinAt

end
end Resonance.UniformShiftSmooth
