import Resonance.ContinuousMicroscopicMatching
import Resonance.ContinuousCollisionEntropy

/-! The complete signed reciprocal difference of the actual microscopic
field, before integration against the same original four-leg measure. -/
open Set MeasureTheory
namespace Resonance.ContinuousMicroscopicDifference
noncomputable section
open ResonantMeasure Thermodynamics WeightedJointMeasure ProfileBanachSmooth
open ContinuousMicroscopicFields MicroscopicCoordinates ContinuousLogPath
open ContinuousCollisionMoments PhaseEnergy Collision CollisionFiber FiberContinuity

def dividedMicro {R : ℝ} (c : ℝ) (f : C(cube R,ℝ)) (θ θc : Parameter) :
    C(cube R,ℝ) := denominatorMap R θ*yField c f (profileMap R θ) (profileMap R θc)

theorem dividedMicro_exact {R : ℝ} (c : ℝ) (f : C(cube R,ℝ))
    (hf : ∀ k,f k≠0) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    dividedMicro c f θ θc=c • (denominatorMap R θc-Ring.inverse f) := by
  have hNc : ∀ k,profileMap R θc k≠0 := by
    intro k
    rw [profileMap_apply hθc]
    exact ne_of_gt (profile_pos hθc k.property)
  ext k
  simp only [dividedMicro,ContinuousMap.mul_apply,ContinuousMap.smul_apply,
    ContinuousMap.sub_apply,smul_eq_mul,denominatorMap_apply,
    yField_apply c f _ _ hf hNc,profileMap_apply hθ,profileMap_apply hθc,
    ring_inverse_apply f hf]
  simpa only [div_eq_mul_inv,mul_comm,profile_eq_inverse_denominator,inv_inv] using
    divided_referenceMicro c (f k) (profile θ k) (profile θc k) (hf k)
      (ne_of_gt (profile_pos hθ k.property)) (ne_of_gt (profile_pos hθc k.property))

theorem dividedMicro_difference_ae {R : ℝ} (c : ℝ) (f : C(cube R,ℝ))
    (hf : ∀ k,f k≠0) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    ∀ᵐ q ∂pairingMeasure R,
      delta (fun i=>continuousExtension R (dividedMicro c f θ θc) (q i))=
        -c*delta (fun i=>(continuousExtension R f (q i))⁻¹) := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R),
    CollisionLinearization.rj_reciprocal_relation_ae R θc] with q hq he
  have hpoint (i : Fin 4) :
      continuousExtension R (dividedMicro c f θ θc) (q i)=
        c*((profile θc (q i))⁻¹-(continuousExtension R f (q i))⁻¹) := by
    rw [continuousExtension_eq R _ ⟨q i,hq.1 i⟩,dividedMicro_exact c f hf hθ hθc,
      ContinuousMap.smul_apply,ContinuousMap.sub_apply,smul_eq_mul,denominatorMap_apply,
      ring_inverse_apply f hf,
      continuousExtension_eq R f ⟨q i,hq.1 i⟩]
    rw [profile_eq_inverse_denominator,inv_inv]
  simp_rw [hpoint]
  unfold delta at he ⊢
  linear_combination c*he

theorem original_test_difference_ae {R : ℝ} (g : C(cube R,ℝ)) (θ : Parameter) :
    ∀ᵐ q ∂pairingMeasure R,
      delta (fun i=>continuousExtension R (denominatorMap R θ*g) (q i))=
        delta (fun i=>continuousExtension R g (q i)/profile θ (q i)) := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  congr 1
  funext i
  rw [continuousExtension_eq R _ ⟨q i,hq.1 i⟩,ContinuousMap.mul_apply,
    denominatorMap_apply,continuousExtension_eq R g ⟨q i,hq.1 i⟩,div_eq_mul_inv]
  rw [profile_eq_inverse_denominator,inv_inv,mul_comm]

end
end Resonance.ContinuousMicroscopicDifference
