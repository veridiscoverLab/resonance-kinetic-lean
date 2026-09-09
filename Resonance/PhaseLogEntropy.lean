import Resonance.ContinuousLogPath
import Resonance.PhaseEnergy
import Resonance.MatchedContinuousTime

/-! Logarithmic entropy on the original full phase space. The exact
transport cancellations are differentiated from the actual Haar-preserving
flow, using its physical clock and the same continuous distribution. -/
open Set MeasureTheory
namespace Resonance.PhaseLogEntropy
noncomputable section
open FreeTransport PhaseEnergy ContinuousLogPath JetCollision SpatialChainRule
open TransportMaterialDerivative JetMomentDynamics MatchedContinuousTime

def entropy (R : ℝ) (f : Distribution R) : ℝ := -integralCLM R (logField f)

theorem entropy_hasDerivWithinAt (R : ℝ) {s : Set ℝ} (hs : Convex ℝ s)
    {f d : ℝ→Distribution R} (hf : ContinuousOn f s) (hd : ContinuousOn d s)
    (hne : ∀ t∈s,∀ z,f t z≠0)
    (hder : ∀ t∈s,HasDerivWithinAt f (d t) s t) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun τ=>entropy R (f τ))
      (-integralCLM R (d t*Ring.inverse (f t))) s t :=
  ((integralCLM R).hasFDerivAt.comp_hasDerivWithinAt t
    (logPath_hasDerivWithinAt hs hf hd hne hder ht)).neg

theorem logField_transport (R t : ℝ) (f : Distribution R) (hf : ∀ z,f z≠0) :
    logField (transport R t f)=transport R t (logField f) := by
  ext z
  rw [logField_apply _ (fun z=>hf (characteristic t z))]
  change Real.log (f (characteristic t z))=logField f (characteristic t z)
  rw [logField_apply _ hf]

theorem entropy_transport (R t : ℝ) (f : Distribution R) (hf : ∀ z,f z≠0) :
    entropy R (transport R t f)=entropy R f := by
  unfold entropy
  rw [logField_transport R t f hf]
  exact congrArg Neg.neg (transport_integral R t (logField f))

theorem entropy_advection_zero (R : ℝ) (p : Space R) (hf : ∀ z,readback p z≠0) :
    integralCLM R (advection R p*Ring.inverse (readback p))=0 := by
  have hc (v : Distribution R) : ContinuousOn (fun t : ℝ=>transport R (-t) v) univ :=
    ((transport_strong_continuous R v).comp continuous_neg).continuousOn
  have h := entropy_hasDerivWithinAt R (s:=univ) convex_univ
    (f:=fun t=>transport R (-t) (readback p)) (d:=fun t=>transport R (-t) (advection R p))
    (hc _) (hc _) (fun t _ z=>hf (characteristic (-t) z))
    (fun t _=>(transport_hasDerivAt R p t).hasDerivWithinAt) (mem_univ (0 : ℝ))
  dsimp only at h
  rw [neg_zero,transport_zero,transport_zero] at h
  have he : (fun t : ℝ=>entropy R (transport R (-t) (readback p)))=
      (fun _ : ℝ=>entropy R (readback p)) := funext (fun t=>entropy_transport R (-t) _ hf)
  rw [he] at h
  have hz := (h.hasDerivAt Filter.univ_mem).unique (hasDerivAt_const 0 (entropy R (readback p)))
  linarith

theorem advection_integration_by_parts (R : ℝ) (p q : Space R) :
    integralCLM R (advection R p*readback q) = -integralCLM R (readback p*advection R q) := by
  have h := (integralCLM R).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((transport_hasDerivAt R p 0).mul (transport_hasDerivAt R q 0))
  simp only [neg_zero,transport_zero] at h
  have he : (fun t : ℝ=>integralCLM R (transport R (-t) (readback p)*transport R (-t) (readback q)))=
      (fun _ : ℝ=>integralCLM R (readback p*readback q)) := by
    funext t
    rw [←transport_mul]
    exact transport_integral R (-t) _
  change HasDerivAt (fun t : ℝ=>integralCLM R (transport R (-t) (readback p)*transport R (-t) (readback q)))
    (integralCLM R (advection R p*readback q+readback p*advection R q)) 0 at h
  rw [he,map_add] at h
  have hz := h.unique (hasDerivAt_const 0 (integralCLM R (readback p*readback q)))
  linarith

theorem original_mild_entropy_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (hne : ∀ t∈Icc 0 T,∀ z,readback (p t) z≠0) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ=>entropy R (readback (p τ)))
      (-c*integralCLM R (SpatialCollision.collision R hR (readback (p t))*Ring.inverse (readback (p t))))
      (Icc 0 T) t := by
  have hf := (readback_continuous R).comp_continuousOn hp
  have h := entropy_hasDerivWithinAt R (convex_Icc 0 T) hf
    ((((SpatialCollision.collision_continuous hR).comp_continuousOn hf).const_smul c).sub
      ((advection_continuous R).comp_continuousOn hp)) hne
    (fun τ hτ=>original_mild_readback_derivative hR hT c p₀ p hp he hτ) ht
  have heq : -integralCLM R ((c • SpatialCollision.collision R hR (readback (p t))-advection R (p t))*
      Ring.inverse (readback (p t))) =
      -c*integralCLM R (SpatialCollision.collision R hR (readback (p t))*Ring.inverse (readback (p t))) := by
    rw [sub_mul,smul_mul_assoc,map_sub,map_smul,entropy_advection_zero R (p t) (hne t ht)]
    simp only [smul_eq_mul,sub_zero,neg_mul]
  exact heq ▸ h

end
end Resonance.PhaseLogEntropy
