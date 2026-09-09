import Resonance.PhaseRelativeEntropy
import Resonance.ContinuousMomentPairing

/-! Exact entropy orthogonality for the actual spatially varying
five-moment match. All three terms use the same original phase integral. -/
open Set MeasureTheory
namespace Resonance.ActualPhasePythagoras
noncomputable section
open FreeTransport PhaseEnergy PhaseRelativeEntropy PhaseLogEntropy ContinuousLogPath
open Thermodynamics ThermodynamicChart ActualMatchedMoments ActualCoframeWeight

theorem entropy_inverse (R : ℝ) (q : Distribution R) (hq : ∀ z,q z≠0) :
    entropy R (Ring.inverse q)= -entropy R q := by
  have hi : ∀ z,Ring.inverse q z≠0 := by
    intro z
    rw [ring_inverse_apply q hq]
    exact inv_ne_zero (hq z)
  have he : logField (Ring.inverse q)= -logField q := by
    ext z
    rw [logField_apply _ hi,ring_inverse_apply q hq,
      ContinuousMap.neg_apply,logField_apply q hq,Real.log_inv]
  simp only [entropy,he,map_neg,neg_neg]

theorem phase_threepoint (R : ℝ) (f q qb : Distribution R) (hq : ∀ z,q z≠0) :
    relativeEntropy R f qb=relativeEntropy R f q+
      relativeEntropy R (Ring.inverse q) qb+
      integralCLM R ((f-Ring.inverse q)*(qb-q)) := by
  have hu : IsUnit q := (ContinuousMap.isUnit_iff_forall_ne_zero q).mpr hq
  have halg : (f*q-1)+(Ring.inverse q*qb-1)+(f-Ring.inverse q)*(qb-q)=f*qb-1 := by
    calc
      _ = f*qb-1+(Ring.inverse q*q-1) := by ring
      _ = _ := by rw [Ring.inverse_mul_cancel q hu,sub_self,add_zero]
  have he := congrArg (integralCLM R) halg
  simp only [map_add] at he
  simp only [relativeEntropy,entropy_inverse R q hq]
  linarith

theorem actual_matched_phase_pythagoras (R : ℝ) (hR : 0 < R) (f : Distribution R)
    (hi : ∀ X,actualMoments R f X∈momentImage R) (a : C(SpatialTorus,Parameter)) :
    relativeEntropy R f (denominatorField R a)=
      relativeEntropy R f (denominatorField R (matchedField R hR f hi))+
      relativeEntropy R (Ring.inverse (denominatorField R (matchedField R hR f hi)))
        (denominatorField R a) := by
  let q := denominatorField R (matchedField R hR f hi)
  have hq : ∀ z,q z≠0 := by
    intro z
    change WeightedPhysicalForm.reciprocalProfile (matchedValue R hR f z.1) z.2≠0
    rw [WeightedPhysicalForm.reciprocalProfile_eq_inv]
    exact inv_ne_zero (WeightedJointMeasure.profile_pos
      (matched_positive R hR f z.1 (hi z.1)) z.2.property).ne'
  have h := phase_threepoint R f q (denominatorField R a) hq
  have hz : integralCLM R ((f-Ring.inverse q)*(denominatorField R a-q))=0 := by
    change integralCLM R ((f-Ring.inverse q)*
      (denominatorField R a-denominatorField R (matchedField R hR f hi)))=0
    rw [←map_sub,mul_comm]
    exact ContinuousMomentPairing.matched_parameter_pairing_zero R hR f hi _
  simpa only [hz,add_zero] using h

end
end Resonance.ActualPhasePythagoras
