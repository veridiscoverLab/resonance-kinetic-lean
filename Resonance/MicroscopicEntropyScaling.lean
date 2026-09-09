import Resonance.OriginalRJEntropyBalance
import Resonance.MicroscopicCoordinates

/-! The c-scaled original entropy identity has exactly the work pairing
used to read the norm of the full four-leg current. -/
open Set MeasureTheory
namespace Resonance.MicroscopicEntropyScaling
noncomputable section
open FreeTransport PhaseEnergy JetCollision ContinuousCollisionMoments ActualMatchedMoments
open Thermodynamics ThermodynamicChart WeightedJointMeasure ActualCoframeWeight
open PhaseRelativeEntropy PhaseCollisionEntropy MicroscopicEntropyWork OriginalRJEntropyBalance
open ContinuousLogPath TransportMaterialDerivative

def reciprocalField (c : ℝ) {R : ℝ} (f q : Distribution R) : Distribution R :=
  c • (1-Ring.inverse (f*q))

theorem reciprocalField_apply (c : ℝ) {R : ℝ} (f q : Distribution R)
    (hf : ∀ z,f z≠0) (hq : ∀ z,q z≠0) (z : Phase R) :
    reciprocalField c f q z=MicroscopicCoordinates.reciprocalMicro c (f z) (q z)⁻¹ := by
  change c*(1-Ring.inverse (f*q) z)=_
  rw [ring_inverse_apply (f*q) (fun z=>mul_ne_zero (hf z) (hq z))]
  simp only [ContinuousMap.mul_apply,MicroscopicCoordinates.reciprocalMicro,mul_inv_rev,div_eq_mul_inv]

theorem scaled_entropyWork (R c : ℝ) (p q : Space R)
    (hp : ∀ z,readback p z≠0) (hq : ∀ z,readback q z≠0) :
    c*entropyWork R p q=integralCLM R
      (reciprocalField c (readback p) (readback q)*(readback p*advection R q)) := by
  unfold entropyWork
  rw [←smul_eq_mul,←map_smul]
  congr 1
  ext z
  change c*((readback p z-Ring.inverse (readback q) z)*advection R q z)=_
  rw [ring_inverse_apply (readback q) hq]
  change c*((readback p z-(readback q z)⁻¹)*advection R q z)=
    reciprocalField c (readback p) (readback q) z*(readback p z*advection R q z)
  rw [reciprocalField_apply c _ _ hp hq]
  simpa only [mul_assoc] using MicroscopicCoordinates.entropy_work_identity c (readback p z)
    (readback q z)⁻¹ (advection R q z) (hp z)

theorem original_RJ_scaled_entropy_balance {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (hpos : ∀ t∈Icc 0 T,∀ z,0 < readback (p t) z)
    (hi : ∀ t∈Icc 0 T,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    (θ₀ : SpatialTorus→Parameter) (hθ₀ : ∀ X,θ₀ X∈positiveDomain R)
    (hinit : ∀ z,readback p₀ z=profile (θ₀ z.1) z.2) :
    c*relativeEntropy R (readback (p T)) (readback (coframeJet R hR (Icc 0 T) p hi T))+
        c^2*(∫ t in (0 : ℝ)..T,phaseProduction R (readback (p t))) =
      ∫ t in (0 : ℝ)..T,integralCLM R
        (reciprocalField c (readback (p t)) (readback (coframeJet R hR (Icc 0 T) p hi t))*
          (readback (p t)*advection R (coframeJet R hR (Icc 0 T) p hi t))) := by
  have h := congrArg (fun x : ℝ=>c*x)
    (original_RJ_microscopic_entropy_balance hR hT c p₀ p hp he hpos hi θ₀ hθ₀ hinit)
  dsimp only at h
  rw [mul_add] at h
  have hiw : (∫ t in (0 : ℝ)..T,c*entropyWork R (p t) (coframeJet R hR (Icc 0 T) p hi t))=
      ∫ t in (0 : ℝ)..T,integralCLM R
        (reciprocalField c (readback (p t)) (readback (coframeJet R hR (Icc 0 T) p hi t))*
          (readback (p t)*advection R (coframeJet R hR (Icc 0 T) p hi t))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    exact scaled_entropyWork R c (p t) _ (fun z=>(hpos t ht' z).ne')
      (fun z=>(coframeJet_positive R hR (Icc 0 T) p hi ht' z).ne')
  rw [intervalIntegral.integral_const_mul] at hiw
  rw [hiw] at h
  convert h using 1; ring

end
end Resonance.MicroscopicEntropyScaling
