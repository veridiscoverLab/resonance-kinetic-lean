import Resonance.WithinEvaluationDerivative
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Uniform continuous-function logarithmic differentiation on the
actual convex time window. No extension across its endpoints is required.
This will be integrated against the original phase measure in cur:main. -/
open Set
namespace Resonance.ContinuousLogPath
noncomputable section
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def logField (f : C(K,ℝ)) : C(K,ℝ) := by
  classical
  exact if hf : ∀ x,f x≠0 then ⟨fun x=>Real.log (f x),f.continuous.log hf⟩ else 0

omit [CompactSpace K] in
theorem logField_apply (f : C(K,ℝ)) (hf : ∀ x,f x≠0) (x : K) :
    logField f x=Real.log (f x) := by simp only [logField,dif_pos hf,ContinuousMap.coe_mk]

omit [CompactSpace K] in
theorem ring_inverse_apply (f : C(K,ℝ)) (hf : ∀ x,f x≠0) (x : K) :
    Ring.inverse f x=(f x)⁻¹ := by
  have hu : IsUnit f := (ContinuousMap.isUnit_iff_forall_ne_zero f).mpr hf
  have h := congrArg (fun g : C(K,ℝ)=>g x) (Ring.inverse_mul_cancel f hu)
  change Ring.inverse f x*f x=1 at h
  simpa only [one_div] using (eq_div_iff (hf x)).mpr h

theorem inversePath_continuousOn {s : Set ℝ} {f : ℝ→C(K,ℝ)}
    (hf : ContinuousOn f s) (hne : ∀ t∈s,∀ x,f t x≠0) :
    ContinuousOn (fun t=>Ring.inverse (f t)) s := by
  intro t ht
  have hu : IsUnit (f t) := (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr (hne t ht)
  have hi := contDiffAt_ringInverse (n:=1) ℝ hu.unit
  rw [IsUnit.unit_spec] at hi
  exact hi.continuousAt.comp_continuousWithinAt (hf t ht)

theorem logPath_hasDerivWithinAt {s : Set ℝ} (hs : Convex ℝ s)
    {f d : ℝ→C(K,ℝ)} (hf : ContinuousOn f s) (hd : ContinuousOn d s)
    (hne : ∀ t∈s,∀ x,f t x≠0)
    (hder : ∀ t∈s,HasDerivWithinAt f (d t) s t) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun τ=>logField (f τ)) (d t*Ring.inverse (f t)) s t := by
  apply WithinEvaluationDerivative.hasDerivWithinAt_of_evaluations hs ht
    ((hd.mul (inversePath_continuousOn hf hne)) t ht)
  intro τ hτ x
  have heval : HasDerivWithinAt (fun u=>f u x) (d τ x) s τ :=
    (ContinuousMap.evalCLM (R:=ℝ) x : C(K,ℝ)→L[ℝ]ℝ).hasFDerivAt.comp_hasDerivWithinAt τ
      (hder τ hτ)
  have h := heval.log (hne τ hτ x)
  have he : (d τ*Ring.inverse (f τ)) x=d τ x/f τ x := by
    rw [ContinuousMap.mul_apply,ring_inverse_apply _ (hne τ hτ),div_eq_mul_inv]
  change HasDerivWithinAt (fun z=>(logField (f z)) x) ((d τ*Ring.inverse (f τ)) x) s τ
  rw [he]
  exact h.congr_of_mem (fun u hu=>logField_apply (f u) (hne u hu) x) hτ

end
end Resonance.ContinuousLogPath
