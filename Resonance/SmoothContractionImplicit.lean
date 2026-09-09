import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! A local smooth branch of a genuinely contracting fixed point.
The partial inverse is constructed by the Neumann theorem, not supplied
as an assumption to the implicit-function theorem. -/
open scoped Topology ContDiff
namespace Resonance.SmoothContractionImplicit
noncomputable section
set_option maxHeartbeats 1800000

theorem actual_local_smooth_fixed_point
    {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
    (T : P×Q→Q) {p : P} {q : Q}
    (hT : ContDiffAt ℝ ∞ T (p,q)) (hfix : T (p,q)=q)
    {L : ℝ} (hL0 : 0≤L) (hL1 : L<1)
    (hLip : ∀ᶠ r in 𝓝 q,‖T (p,r)-T (p,q)‖≤L*‖r-q‖) :
    ∃g : P→Q,ContDiffAt ℝ ∞ g p ∧ g p=q ∧
      ∀ᶠ a in 𝓝 p,T (a,g a)=g a := by
  let f : P×Q→Q := fun a=>a.2-T a
  have hf : ContDiffAt ℝ ∞ f (p,q) := contDiffAt_snd.sub hT
  have hslice : HasFDerivAt (fun r : Q=>(p,r)) (ContinuousLinearMap.inr ℝ P Q) q := by
    convert (hasFDerivAt_const p q).prodMk (hasFDerivAt_id q) using 1
  have hTs : HasFDerivAt (fun r=>T (p,r))
      ((fderiv ℝ T (p,q)).comp (ContinuousLinearMap.inr ℝ P Q)) q :=
    (hT.differentiableAt (by simp)).hasFDerivAt.comp q hslice
  have hd : (fderiv ℝ f (p,q)).comp (ContinuousLinearMap.inr ℝ P Q)=
      (1 : Q→L[ℝ]Q)-fderiv ℝ (fun r=>T (p,r)) q := by
    have hfs := (hf.differentiableAt (by simp)).hasFDerivAt.comp q hslice
    have hfs' := (hasFDerivAt_id q).sub hTs
    have he := hfs.unique hfs'
    rw [hTs.fderiv] at ⊢
    exact he
  have hn : ‖fderiv ℝ (fun r=>T (p,r)) q‖<1 :=
    (norm_fderiv_le_of_lip' ℝ hL0 hLip).trans_lt hL1
  obtain ⟨U,hU⟩ := isUnit_one_sub_of_norm_lt_one hn
  have hi : ((fderiv ℝ f (p,q)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible := by
    rw [hd]
    exact ⟨ContinuousLinearEquiv.ofUnit U,hU⟩
  let g := hf.implicitFunction (by simp) hi
  refine ⟨g,hf.contDiffAt_implicitFunction (by simp) hi,
    hf.implicitFunction_apply_self (by simp) hi,?_⟩
  filter_upwards [hf.eventually_apply_implicitFunction (by simp) hi] with a ha
  change g a-T (a,g a)=q-T (p,q) at ha
  rw [hfix,sub_self] at ha
  exact (sub_eq_zero.mp ha).symm

end
end Resonance.SmoothContractionImplicit
