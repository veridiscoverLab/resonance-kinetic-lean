import Resonance.PhaseCollisionEntropy
import Resonance.EntropyBalanceAlgebra
import Resonance.CoframeEntropyCancellation

/-! The exact microscopic entropy balance of the original nonlinear
mild solution. The reciprocal coframe is its actual five-moment matching.
No independent macro evolution equation or entropy balance is assumed. -/
open Set MeasureTheory
namespace Resonance.ActualMicroscopicEntropy
noncomputable section
open FreeTransport PhaseEnergy JetCollision TransportMaterialDerivative
open ContinuousCollisionMoments ActualMatchedMoments Thermodynamics ThermodynamicChart
open MatchedContinuousTime ActualCoframeWeight CoframeEntropyCancellation
open PhaseLogEntropy PhaseCollisionEntropy PhaseRelativeEntropy

theorem original_mild_microscopic_entropy_derivative {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (hpos : ∀ t∈Icc 0 T,∀ z,0 < readback (p t) z)
    (hi : ∀ t∈Icc 0 T,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ=>relativeEntropy R (readback (p τ))
        (readback (coframeJet R hR (Icc 0 T) p hi τ)))
      (-c*phaseProduction R (readback (p t))+
        integralCLM R ((readback (p t)-Ring.inverse (readback (coframeJet R hR (Icc 0 T) p hi t)))*
          advection R (coframeJet R hR (Icc 0 T) p hi t))) (Icc 0 T) t := by
  let f : ℝ→Distribution R := fun τ=>readback (p τ)
  let d : ℝ→Distribution R := fun τ=>c • SpatialCollision.collision R hR.le (f τ)-advection R (p τ)
  have hf : ContinuousOn f (Icc 0 T) := (readback_continuous R).comp_continuousOn hp
  have hd : ContinuousOn d (Icc 0 T) :=
    (((SpatialCollision.collision_continuous hR.le).comp_continuousOn hf).const_smul c).sub
      ((advection_continuous R).comp_continuousOn hp)
  have hq : ContinuousOn (fun τ=>readback (coframeJet R hR (Icc 0 T) p hi τ)) (Icc 0 T) := by
    simp only [coframeJet_readback]
    exact (denominatorField R).continuous.comp_continuousOn
      (parameterPath_continuousOn R hR (Icc 0 T) f hi hf)
  have hdq : ContinuousOn (coframeTimeRate R hR (Icc 0 T) c p hi) (Icc 0 T) :=
    (denominatorField R).continuous.comp_continuousOn
      (parameterRatePath_continuousOn R hR (Icc 0 T) f d hi hf hd)
  have h := relativeEntropy_hasDerivWithinAt R (convex_Icc 0 T) hf hq hd hdq
    (fun τ hτ z=>(hpos τ hτ z).ne')
    (fun τ hτ z=>(coframeJet_positive R hR (Icc 0 T) p hi hτ z).ne')
    (fun τ hτ=>JetMomentDynamics.original_mild_readback_derivative hR.le hT c p₀ p hp he hτ)
    (fun τ hτ=>original_mild_coframe_strong_derivative hR hT c p₀ p hp he hi hτ) ht
  have heq := EntropyBalanceAlgebra.assemble R c (phaseProduction R (f t))
    (f t) (readback (coframeJet R hR (Icc 0 T) p hi t))
    (SpatialCollision.collision R hR.le (f t)) (advection R (p t))
    (advection R (coframeJet R hR (Icc 0 T) p hi t)) (coframeTimeRate R hR (Icc 0 T) c p hi t)
    (coframe_time_pairing_zero R hR (Icc 0 T) c p hi ht)
    (coframe_collision_pairing_zero R hR (Icc 0 T) p hi t)
    (phase_collision_production hR.le (f t) (hpos t ht))
    (entropy_advection_zero R (p t) (fun z=>(hpos t ht z).ne'))
    (advection_integration_by_parts R (p t) (coframeJet R hR (Icc 0 T) p hi t))
    (coframe_equilibrium_transport_zero R hR (Icc 0 T) p hi ht)
  exact heq ▸ h

end
end Resonance.ActualMicroscopicEntropy
