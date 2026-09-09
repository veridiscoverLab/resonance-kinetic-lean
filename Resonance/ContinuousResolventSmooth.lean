import Resonance.ContinuousAugmentedResolvent

/-! Genuine C(D)-valued smooth dependence of the original augmented
regularized inverse for every positive fixed shift. Its inverse is proved
from the actual equation, not postulated or inferred from an L∞ inverse. -/
open Set
open scoped ContDiff
namespace Resonance.ContinuousResolventSmooth
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics ProfileBanachSmooth ContinuousSourceCoordinates
open BasisBanachSmooth ContinuousLinearizedUniqueness ContinuousAugmentedResolvent

theorem linearAction_contDiffAt {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (linearAction hR) θ := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ (FiberContinuity.collisionMap R hR)) :=
    (contDiff_infty_iff_fderiv.mp (CollisionMultilinear.collisionMap_contDiff hR ∞)).2
  unfold linearAction
  exact (((ContinuousLinearMap.mul ℝ C(cube R,ℝ)).contDiff).comp
    (denominatorMap R).contDiff).contDiffAt.clm_comp
      ((hd.contDiffAt.comp θ (profileMap_contDiffAt hθ)).clm_comp
        ((ContinuousLinearMap.mul ℝ C(cube R,ℝ)).contDiff.contDiffAt.comp θ (profileMap_contDiffAt hθ)))

theorem correctionMap_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (correctionMap hR) θ :=
  (synthesisContinuousFamily_contDiffAt hθ).clm_comp
    ((analysisFamily_contDiffAt hR hθ).clm_comp contDiffAt_const)

theorem augmented_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) :
    ContDiffAt ℝ ∞ (fun β=>augmented hR β s) θ :=
  (contDiffAt_const.sub ((linearAction_contDiffAt hR.le hθ).const_smul s)).add
    ((correctionMap_contDiffAt hR hθ).const_smul s)

def inverseFamily {R : ℝ} (hR : 0<R) (s : ℝ) (θ : Parameter) : X R→L[ℝ]X R :=
  Ring.inverse (augmented hR θ s)

theorem inverseFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) :
    inverseFamily hR s θ=outputCLM hR hθ hs := Ring.inverse_unit (augmentedUnit hR hθ hs)

theorem actual_continuous_inverse_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) :
    ContDiffAt ℝ ∞ (inverseFamily hR s) θ :=
  (contDiffAt_ringInverse (𝕜:=ℝ) (n:=∞) (augmentedUnit hR hθ hs)).comp θ
    (augmented_contDiffAt hR hθ s)

theorem actual_continuous_inverse_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) (F : X R) :
    inverseFamily hR s θ F=ContinuousRegularizedEquation.output hR hθ hs F := by
  rw [inverseFamily_eq hR hθ hs]
  rfl

end
end Resonance.ContinuousResolventSmooth
