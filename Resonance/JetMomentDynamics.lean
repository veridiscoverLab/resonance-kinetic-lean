import Resonance.ContinuousCollisionMoments
import Resonance.TransportMaterialDerivative

/-! The time derivative and local five-moment balance of the same actual
compatible mild solution, with its original velocity and physical clock. -/
open Set MeasureTheory
namespace Resonance.JetMomentDynamics
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace
open TransportMaterialDerivative ContinuousCollisionMoments
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

theorem advection_transport (R t : ℝ) (p : Space R) :
    advection R (JetTransport.map R t p)=transport R t (advection R p) := by
  have h1 := transport_hasDerivAt R (JetTransport.map R t p) 0
  simp only [neg_zero,transport_zero] at h1
  have h2 := (transportCLM R t).hasFDerivAt.comp_hasDerivAt 0 (transport_hasDerivAt R p 0)
  simp only [neg_zero,transport_zero] at h2
  have he : (fun s => transport R (-s) (readback (JetTransport.map R t p))) =
      fun s => transportCLM R t (transport R (-s) (readback p)) := by
    funext s
    change transport R (-s) (readback (JetTransport.map R t p))=
      transport R t (transport R (-s) (readback p))
    rw [JetTransport.map_readback,transport_add_time,transport_add_time,add_comm]
  rw [he] at h1
  exact h1.unique h2

theorem forward_transport_hasDerivAt (R : ℝ) (p : Space R) (t : ℝ) :
    HasDerivAt (fun τ => transport R τ (readback p))
      (-(transport R t (advection R p))) t := by
  have hn : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
  have h := (transport_hasDerivAt R p (-t)).scomp t hn
  simpa [Function.comp_def] using h

theorem physical_readback_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => readback (JetTransport.map R τ (g τ)))
      (c • SpatialCollision.collision R hR (readback (JetTransport.map R t (g t)))-
        advection R (JetTransport.map R t (g t))) (Icc 0 T) t := by
  have hg' := (JetLocalKinetics.readbackOperator R).hasFDerivAt.comp_hasDerivWithinAt t
    (JetMildEquation.moving_frame_hasDerivWithinAt hR hT c p₀ g hg he t ht)
  have h := strong_family_hasDerivWithinAt (fun τ => transportCLM R τ)
    (TransportDuhamel.transport_joint_continuous R) hg'
    (forward_transport_hasDerivAt R (g t) t).hasDerivWithinAt
  change HasDerivWithinAt (fun τ => transport R τ (readback (g τ)))
    (transport R t (readback (JetKineticField.field R hR c t (g t)))+
      -(transport R t (advection R (g t)))) (Icc 0 T) t at h
  rw [JetKineticField.field_readback] at h
  simp only [KineticField.field,transport_smul,transport_add_time,add_neg_cancel,transport_zero,
    ←JetTransport.map_readback,←advection_transport,←sub_eq_add_neg] at h
  exact h

theorem original_mild_readback_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => readback (p τ))
      (c • SpatialCollision.collision R hR (readback (p t))-advection R (p t)) (Icc 0 T) t := by
  have h := physical_readback_derivative hR hT c p₀ (JetAmplitudeBounds.toFrame R p)
    (JetAmplitudeBounds.toFrame_continuousOn hp)
    (JetAmplitudeBounds.actual_mild_to_moving_frame hR c p₀ p hp he) ht
  simpa only [JetAmplitudeBounds.toFrame,JetTransport.map_add_time,add_neg_cancel,
    JetTransport.map_zero_time] using h

/-- Every original quadratic moment of the actual solution has the transport
flux derivative; no collision term remains and no Euler equation is assumed. -/
theorem original_mild_moment_time_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (θ : Thermodynamics.Parameter) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => spatialMoment R θ (readback (p τ)))
      (-spatialMoment R θ (advection R (p t))) (Icc 0 T) t := by
  have h := (spatialMoment R θ).hasFDerivAt.comp_hasDerivWithinAt t
    (original_mild_readback_derivative hR hT c p₀ p hp he ht)
  simpa only [map_sub,map_smul,spatial_collision_five_moments hR,smul_zero,zero_sub] using h

def coordinateVelocity (R : ℝ) (j : Fin 3) : CubeFunction R :=
  ⟨fun k => 2*(k : ResonantMeasure.E) j,
    continuous_const.mul (((continuous_apply j).comp
      WeightedJointMeasure.coordinates_continuous).comp continuous_subtype_val)⟩

/-- The flux uses the original velocity, without any projected moment closure. -/
def fluxMoment (R : ℝ) (θ : Thermodynamics.Parameter) (j : Fin 3) : CubeFunction R →L[ℝ] ℝ :=
  (moment R θ).comp
    (ContinuousLinearMap.mul ℝ (CubeFunction R) (coordinateVelocity R j))

theorem fluxMoment_integral (R : ℝ) (θ : Thermodynamics.Parameter) (j : Fin 3)
    (f : CubeFunction R) :
    fluxMoment R θ j f = ∫ k,WeightedPhysicalForm.reciprocalProfile θ k*
      ((2*(k : ResonantMeasure.E) j)*f k) ∂PhaseEnergy.momentumMeasure R := rfl

theorem velocity_coordinate_sum (R : ℝ) (k : MomentumDomain R) :
    velocity R k = ∑ j : Fin 3,(2*(k : ResonantMeasure.E) j) •
      (Pi.single j (1 : ℝ) : RealPosition) := by
  ext i
  simp [velocity,Finset.sum_apply,Pi.single_apply]

/-- Differentiation is only in the common real lift of the spatial torus.
No regularity in momentum is used. -/
theorem flux_hasFDerivAt (R : ℝ) (θ : Thermodynamics.Parameter) (j : Fin 3)
    (p : Space R) (x : RealPosition) :
    HasFDerivAt (fun y => fluxMoment R θ j (realLift (readback p) y))
      ((fluxMoment R θ j).comp (p.val.2.1 (torusQuotient x))) x := by
  exact (fluxMoment R θ j).hasFDerivAt.comp x (p.property.1 x)

def fluxDivergence (R : ℝ) (θ : Thermodynamics.Parameter) (p : Space R)
    (x : RealPosition) : ℝ :=
  ∑ j : Fin 3,fderiv ℝ (fun y => fluxMoment R θ j (realLift (readback p) y)) x
    (Pi.single j 1)

theorem moment_advection_eq_fluxDivergence (R : ℝ) (θ : Thermodynamics.Parameter)
    (p : Space R) (x : RealPosition) :
    spatialMoment R θ (advection R p) (torusQuotient x)=fluxDivergence R θ p x := by
  have he : (advection R p).curry (torusQuotient x)=
      ∑ j : Fin 3,coordinateVelocity R j *
        (p.val.2.1 (torusQuotient x) (Pi.single j (1 : ℝ))) := by
    ext k
    change p.val.2.1 (torusQuotient x) (velocity R k) k = _
    rw [velocity_coordinate_sum,map_sum]
    simp [ContinuousMap.sum_apply,map_smul,coordinateVelocity]
  change moment R θ ((advection R p).curry (torusQuotient x))=_
  rw [he,map_sum]
  unfold fluxDivergence
  apply Finset.sum_congr rfl
  intro j _
  rw [(flux_hasFDerivAt R θ j p x).fderiv]
  rfl

/-- The local physical five-moment conservation law of the original mild
solution. It retains all spatial positions, momenta and the same clock c. -/
theorem original_mild_local_five_balance {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (θ : Thermodynamics.Parameter) (x : RealPosition) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => spatialMoment R θ (readback (p τ)) (torusQuotient x))
      (-fluxDivergence R θ (p t) x) (Icc 0 T) t := by
  have h := (ContinuousMap.evalCLM (R := ℝ) (torusQuotient x)).hasFDerivAt.comp_hasDerivWithinAt t
    (original_mild_moment_time_derivative hR hT c p₀ p hp he θ ht)
  simpa only [ContinuousMap.evalCLM_apply,ContinuousMap.neg_apply,
    moment_advection_eq_fluxDivergence] using h

#check advection_transport
#check forward_transport_hasDerivAt
#check physical_readback_derivative
#check original_mild_readback_derivative
#check original_mild_moment_time_derivative
#check fluxMoment_integral
#check velocity_coordinate_sum
#check flux_hasFDerivAt
#check moment_advection_eq_fluxDivergence
#check original_mild_local_five_balance
#print axioms advection_transport
#print axioms forward_transport_hasDerivAt
#print axioms physical_readback_derivative
#print axioms original_mild_readback_derivative
#print axioms original_mild_moment_time_derivative
#print axioms fluxMoment_integral
#print axioms velocity_coordinate_sum
#print axioms flux_hasFDerivAt
#print axioms moment_advection_eq_fluxDivergence
#print axioms original_mild_local_five_balance

end
end Resonance.JetMomentDynamics
