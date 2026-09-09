import Resonance.ActualMicroscopicEntropy
import Resonance.MicroscopicEntropyWork
import Resonance.EntropyWindowCalculus

/-! The exact full-window entropy identity, integrated from the same
original initial time. No boundary time differentiability is added. -/
open Set MeasureTheory
namespace Resonance.ActualEntropyIntegral
noncomputable section
open FreeTransport PhaseEnergy JetCollision TransportMaterialDerivative
open ContinuousCollisionMoments ActualMatchedMoments Thermodynamics ThermodynamicChart
open MatchedContinuousTime ActualCoframeWeight PhaseRelativeEntropy PhaseCollisionEntropy
open ActualMicroscopicEntropy MicroscopicEntropyWork EntropyWindowCalculus

theorem original_mild_microscopic_entropy_integral {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (hpos : ∀ t∈Icc 0 T,∀ z,0 < readback (p t) z)
    (hi : ∀ t∈Icc 0 T,∀ X,actualMoments R (readback (p t)) X∈momentImage R) :
    relativeEntropy R (readback (p T)) (readback (coframeJet R hR (Icc 0 T) p hi T))+
        c*(∫ t in (0 : ℝ)..T,phaseProduction R (readback (p t))) =
      relativeEntropy R (readback (p 0)) (readback (coframeJet R hR (Icc 0 T) p hi 0))+
        ∫ t in (0 : ℝ)..T,entropyWork R (p t) (coframeJet R hR (Icc 0 T) p hi t) := by
  apply integrate_entropy_balance (c:=c) hT
    (fun t=>relativeEntropy R (readback (p t)) (readback (coframeJet R hR (Icc 0 T) p hi t)))
    (fun t=>phaseProduction R (readback (p t)))
    (fun t=>entropyWork R (p t) (coframeJet R hR (Icc 0 T) p hi t))
  · exact phaseProduction_continuousOn hR.le ((readback_continuous R).comp_continuousOn hp) hpos
  · exact actual_entropyWork_continuousOn R hR (Icc 0 T) p hp hi
  · intro t ht
    exact original_mild_microscopic_entropy_derivative hR hT c p₀ p hp he hpos hi ht

end
end Resonance.ActualEntropyIntegral
