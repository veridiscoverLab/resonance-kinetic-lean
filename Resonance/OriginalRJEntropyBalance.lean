import Resonance.ActualEntropyIntegral
import Resonance.ActualRJEntropy

/-! The original microscopic entropy identity with its actual RJ initial
condition. It starts at time zero and keeps the whole positive mild window. -/
open Set MeasureTheory
namespace Resonance.OriginalRJEntropyBalance
noncomputable section
open FreeTransport PhaseEnergy JetCollision ContinuousCollisionMoments ActualMatchedMoments
open Thermodynamics ThermodynamicChart WeightedJointMeasure ActualCoframeWeight
open PhaseRelativeEntropy PhaseCollisionEntropy MicroscopicEntropyWork
open ActualEntropyIntegral ActualRJEntropy

theorem original_RJ_microscopic_entropy_balance {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (hpos : ∀ t∈Icc 0 T,∀ z,0 < readback (p t) z)
    (hi : ∀ t∈Icc 0 T,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    (θ₀ : SpatialTorus→Parameter) (hθ₀ : ∀ X,θ₀ X∈positiveDomain R)
    (hinit : ∀ z,readback p₀ z=profile (θ₀ z.1) z.2) :
    relativeEntropy R (readback (p T)) (readback (coframeJet R hR (Icc 0 T) p hi T))+
        c*(∫ t in (0 : ℝ)..T,phaseProduction R (readback (p t))) =
      ∫ t in (0 : ℝ)..T,entropyWork R (p t) (coframeJet R hR (Icc 0 T) p hi t) := by
  have h0 : readback (p 0)=readback p₀ := by
    have h := he 0 ⟨le_rfl,hT⟩
    simpa only [transport_zero,intervalIntegral.integral_same,add_zero] using h
  have hHz := coframe_entropy_zero_of_localRJ R hR (Icc 0 T) p hi ⟨le_rfl,hT⟩
    θ₀ hθ₀ (fun z=>by rw [h0]; exact hinit z)
  have h := original_mild_microscopic_entropy_integral hR hT c p₀ p hp he hpos hi
  simpa only [hHz,zero_add] using h

end
end Resonance.OriginalRJEntropyBalance
