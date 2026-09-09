import Resonance.ContinuousResolventJets
import Resonance.NonlinearCellUniqueness

/-! Smooth actual nonlinear iteration on its closed two-norm graph.
The continuous output, full cubic, and true profile are differentiated
as Banach-valued maps before any implicit branch is introduced. -/
open Set
open scoped ContDiff Topology
namespace Resonance.GraphResolventSmooth
noncomputable section
set_option maxHeartbeats 2200000
open ResonantMeasure Thermodynamics ProfileBanachSmooth RegularizedGraphNorm
open ContinuousResolventSmooth NormalizedCubicRemainder ContinuousLinearizedUniqueness

def liftMap {R : ℝ} (hR : 0≤R) (s : ℝ) : X R→L[ℝ]graphSpace hR s :=
  ((ContinuousLinearMap.id ℝ (X R)).prod (s • weightMap hR)).codRestrict
    (graphSpace hR s) (fun q=>(lift hR s q).property)

def readMap {R : ℝ} (hR : 0≤R) (s : ℝ) : graphSpace hR s→L[ℝ]X R :=
  (ContinuousLinearMap.fst ℝ (X R) (X R)).comp (graphSpace hR s).subtypeL

theorem liftMap_apply {R : ℝ} (hR : 0≤R) (s : ℝ) (q : X R) :
    liftMap hR s q=lift hR s q := rfl

theorem readMap_apply {R : ℝ} (hR : 0≤R) (s : ℝ) (q : graphSpace hR s) :
    readMap hR s q=read q := rfl

theorem actual_remainder_joint_contDiffAt {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (q : X R) :
    ContDiffAt ℝ ∞ (fun a : Parameter×X R=>remainder R hR a.1 a.2) (θ,q) := by
  let f : Parameter×X R→X R := fun a=>denominatorMap R a.1*
    FiberContinuity.collisionMap R hR (profileMap R a.1*(1+a.2))-linearAction hR a.1 a.2
  have hprofile : ContDiffAt ℝ ∞ (fun a : Parameter×X R=>profileMap R a.1) (θ,q) :=
    ContDiffAt.comp (g:=profileMap R) (f:=fun a : Parameter×X R=>a.1)
      (θ,q) (profileMap_contDiffAt hθ) contDiffAt_fst
  have hden : ContDiffAt ℝ ∞ (fun a : Parameter×X R=>denominatorMap R a.1) (θ,q) :=
    ((denominatorMap R).contDiff.comp contDiff_fst).contDiffAt
  have hf : ContDiffAt ℝ ∞ f (θ,q) :=
    ((hden.mul
      ((CollisionMultilinear.collisionMap_contDiff hR ∞).contDiffAt.comp (θ,q)
        (hprofile.mul (contDiffAt_const.add contDiffAt_snd)))).sub
      (((linearAction_contDiffAt hR hθ).comp (θ,q) contDiffAt_fst).clm_apply contDiffAt_snd))
  apply hf.congr_of_eventuallyEq
  filter_upwards [(positiveDomain_isOpen R).preimage continuous_fst |>.eventually_mem (show
    (θ,q)∈Prod.fst ⁻¹' positiveDomain R from hθ)] with a ha
  dsimp [f]
  rw [actual_normalized_decomposition hR ha]
  change remainder R hR a.1 a.2=_+remainder R hR a.1 a.2-
    (denominatorMap R a.1*fderiv ℝ (FiberContinuity.collisionMap R hR)
      (profileMap R a.1) (profileMap R a.1*a.2))
  abel

def jointStep {R : ℝ} (hR : 0<R) (s : ℝ) :
    (Parameter×X R)×graphSpace hR.le s → graphSpace hR.le s := fun a=>
  liftMap hR.le s (inverseFamily hR s a.1.1
    (a.1.2+s • remainder R hR.le a.1.1 (readMap hR.le s a.2)))

theorem jointStep_eq {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 1 ≤ s) (F : X R) (q : graphSpace hR.le s) :
    jointStep hR s ((θ,F),q)=NonlinearRegularizedStep.step hR hθ hs F q := by
  unfold jointStep
  rw [actual_continuous_inverse_apply hR hθ (zero_lt_one.trans_le hs)]
  rfl

theorem jointStep_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) (F : X R) (q : graphSpace hR.le s) :
    ContDiffAt ℝ ∞ (jointStep hR s) ((θ,F),q) := by
  have hp : ContDiffAt ℝ ∞ (fun a : (Parameter×X R)×graphSpace hR.le s=>a.1.1) ((θ,F),q) :=
    contDiffAt_fst.fst
  have hr : ContDiffAt ℝ ∞ (fun a : (Parameter×X R)×graphSpace hR.le s=>
      readMap hR.le s a.2) ((θ,F),q) := (readMap hR.le s).contDiff.contDiffAt.comp ((θ,F),q) contDiffAt_snd
  have hi : ContDiffAt ℝ ∞ (fun a : (Parameter×X R)×graphSpace hR.le s=>
      inverseFamily hR s a.1.1) ((θ,F),q) :=
    ContDiffAt.comp (g:=inverseFamily hR s) (f:=fun a : (Parameter×X R)×graphSpace hR.le s=>a.1.1)
      ((θ,F),q) (actual_continuous_inverse_contDiffAt hR hθ hs) hp
  have hrem : ContDiffAt ℝ ∞ (fun a : (Parameter×X R)×graphSpace hR.le s=>
      remainder R hR.le a.1.1 (readMap hR.le s a.2)) ((θ,F),q) :=
    ContDiffAt.comp (g:=fun b : Parameter×X R=>remainder R hR.le b.1 b.2)
      (f:=fun a : (Parameter×X R)×graphSpace hR.le s=>(a.1.1,readMap hR.le s a.2))
      ((θ,F),q) (actual_remainder_joint_contDiffAt hR.le hθ (read q)) (hp.prodMk hr)
  exact (liftMap hR.le s).contDiff.contDiffAt.comp ((θ,F),q)
    (hi.clm_apply (contDiffAt_fst.snd.add (hrem.const_smul s)))

end
end Resonance.GraphResolventSmooth
