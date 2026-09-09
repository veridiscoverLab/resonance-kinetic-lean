import Resonance.PhaseLogEntropy

/-! The exact time derivative of relative entropy in the moving
reciprocal coframe. Both distribution and coframe remain actual functions
on the original phase space; the coframe derivative is retained here. -/
open Set MeasureTheory
namespace Resonance.PhaseRelativeEntropy
noncomputable section
open FreeTransport PhaseEnergy PhaseLogEntropy ContinuousLogPath

def relativeEntropy (R : ℝ) (f q : Distribution R) : ℝ :=
  integralCLM R (f*q-1)+entropy R f+entropy R q

theorem relativeEntropy_integral (R : ℝ) (f q : Distribution R)
    (hf : ∀ z,0 < f z) (hq : ∀ z,0 < q z) :
    relativeEntropy R f q=∫ z,f z*q z-1-Real.log (f z*q z) ∂phaseMeasure R := by
  unfold relativeEntropy entropy
  rw [←map_neg,←map_add,←map_neg,←map_add]
  change (∫ z,(f*q-1+-logField f+-logField q) z ∂phaseMeasure R)=_
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.neg_apply,
    ContinuousMap.mul_apply,ContinuousMap.one_apply,
    logField_apply _ (fun z=>(hf z).ne'),logField_apply _ (fun z=>(hq z).ne'),
    Real.log_mul (hf z).ne' (hq z).ne']
  ring

theorem derivative_algebra (R : ℝ) (f q df dq : Distribution R) :
    integralCLM R (df*q+f*dq)-integralCLM R (df*Ring.inverse f)-integralCLM R (dq*Ring.inverse q)=
      integralCLM R (df*(q-Ring.inverse f)+(f-Ring.inverse q)*dq) := by
  rw [←map_sub,←map_sub]
  congr 1
  ring

theorem relativeEntropy_hasDerivWithinAt (R : ℝ) {s : Set ℝ} (hs : Convex ℝ s)
    {f q df dq : ℝ→Distribution R}
    (hf : ContinuousOn f s) (hq : ContinuousOn q s)
    (hdf : ContinuousOn df s) (hdq : ContinuousOn dq s)
    (hnf : ∀ t∈s,∀ z,f t z≠0) (hnq : ∀ t∈s,∀ z,q t z≠0)
    (hft : ∀ t∈s,HasDerivWithinAt f (df t) s t)
    (hqt : ∀ t∈s,HasDerivWithinAt q (dq t) s t) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun τ=>relativeEntropy R (f τ) (q τ))
      (integralCLM R (df t*(q t-Ring.inverse (f t))+(f t-Ring.inverse (q t))*dq t)) s t := by
  have hp := (integralCLM R).hasFDerivAt.comp_hasDerivWithinAt t
    (((hft t ht).mul (hqt t ht)).sub_const (1 : Distribution R))
  have h := (hp.add (entropy_hasDerivWithinAt R hs hf hdf hnf hft ht)).add
    (entropy_hasDerivWithinAt R hs hq hdq hnq hqt ht)
  have he := derivative_algebra R (f t) (q t) (df t) (dq t)
  simp only [sub_eq_add_neg] at he
  exact he ▸ h

end
end Resonance.PhaseRelativeEntropy
