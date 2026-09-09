import Resonance.CoframeEntropyCancellation

/-! The same entropy work has a continuous representation without
requiring a time derivative in the C³ jet norm of the matched coframe. -/
open Set MeasureTheory
namespace Resonance.MicroscopicEntropyWork
noncomputable section
open FreeTransport PhaseEnergy JetCollision TransportMaterialDerivative
open ContinuousCollisionMoments ActualMatchedMoments Thermodynamics ThermodynamicChart
open MatchedContinuousTime ActualCoframeWeight CoframeEntropyCancellation PhaseLogEntropy

def entropyWork (R : ℝ) (p q : Space R) : ℝ :=
  integralCLM R ((readback p-Ring.inverse (readback q))*advection R q)

theorem entropyWork_eq (R : ℝ) (p q : Space R) (hq : ∀ z,readback q z≠0) :
    entropyWork R p q = -integralCLM R (advection R p*readback q) := by
  unfold entropyWork
  rw [sub_mul,map_sub,mul_comm (Ring.inverse (readback q)),entropy_advection_zero R q hq,sub_zero]
  have h := advection_integration_by_parts R p q
  linarith

theorem actual_entropyWork_continuousOn (R : ℝ) (hR : 0 < R) (s : Set ℝ) (p : ℝ→Space R)
    (hp : ContinuousOn p s)
    (hi : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R) :
    ContinuousOn (fun t=>entropyWork R (p t) (coframeJet R hR s p hi t)) s := by
  have hf := (readback_continuous R).comp_continuousOn hp
  have hq : ContinuousOn (fun t=>readback (coframeJet R hR s p hi t)) s := by
    simp only [coframeJet_readback]
    exact (denominatorField R).continuous.comp_continuousOn
      (parameterPath_continuousOn R hR s _ hi hf)
  have h := ((integralCLM R).continuous.comp_continuousOn
    (((advection_continuous R).comp_continuousOn hp).mul hq)).neg
  exact h.congr (fun t ht=>entropyWork_eq R (p t) _
    (fun z=>(coframeJet_positive R hR s p hi ht z).ne'))

end
end Resonance.MicroscopicEntropyWork
