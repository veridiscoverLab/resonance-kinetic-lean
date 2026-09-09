import Resonance.RelativeCoframeJets

/-! One material derivative of the actual first and second spatial jets uses
only the already compatible third spatial jet. No fourth derivative is added. -/
open Set Function
open scoped ContDiff
namespace Resonance.LowSpatialMaterialDerivative
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace SpatialTranslationOrbit
open SpatialJetDescent TransportMaterialDerivative JetEnergy
set_option maxHeartbeats 1500000

theorem derivative_at_quotient (R : ℝ) (p : Space R) (n : ℕ) (hn : n≤3)
    (v : Fin n→RealPosition) (x : RealPosition) (k : MomentumDomain R) :
    spatialDerivative R n hn v p (torusQuotient x,k)=
      iteratedFDeriv ℝ n (realLift (readback p)) x v k := by
  have h := (JetTransport.evaluationCLM R (torusQuotient x)).iteratedFDeriv_comp_left
    (x := (0 : RealPosition)) (distributionOrbit_contDiff p).contDiffAt (by exact_mod_cast hn)
  change iteratedFDeriv ℝ n (JetTransport.evaluationCLM R (torusQuotient x) ∘
    distributionOrbit (readback p)) 0=_ at h
  have he : JetTransport.evaluationCLM R (torusQuotient x) ∘ distributionOrbit (readback p)=
      fun y => realLift (readback p) (y+x) := by
    funext y
    ext k
    change readback p (torusQuotient y+torusQuotient x,k)=readback p (torusQuotient (y+x),k)
    rw [torusQuotient_add]
  rw [he,iteratedFDeriv_comp_add_right,zero_add] at h
  exact (congrArg (fun A => A v k) h).symm

def firstField (R : ℝ) (p : Space R) (a : RealPosition) : C(SpatialTorus,V0 R) :=
  ⟨fun X => p.val.2.1 X a,p.val.2.1.continuous.clm_apply continuous_const⟩

def secondField (R : ℝ) (p : Space R) (a b : RealPosition) : C(SpatialTorus,V0 R) :=
  ⟨fun X => p.val.2.2.1 X a b,
    (p.val.2.2.1.continuous.clm_apply continuous_const).clm_apply continuous_const⟩

theorem firstField_actual (R : ℝ) (p : Space R) (a : RealPosition) :
    ContinuousMap.uncurry (firstField R p a)=spatialDerivative R 1 (by omega) ![a] p := by
  ext z
  obtain ⟨x,hx⟩ := torusQuotient_surjective z.1
  have hz : z=(torusQuotient x,z.2) := Prod.ext hx.symm rfl
  rw [hz,derivative_at_quotient,iteratedFDeriv_one_apply]
  change p.val.2.1 (torusQuotient x) a z.2=(fderiv ℝ (fieldLift p.val.1) x) a z.2
  rw [compatible_first_fderiv p.property]

theorem secondField_actual (R : ℝ) (p : Space R) (a b : RealPosition) :
    ContinuousMap.uncurry (secondField R p a b)=spatialDerivative R 2 (by omega) ![a,b] p := by
  ext z
  obtain ⟨x,hx⟩ := torusQuotient_surjective z.1
  have hz : z=(torusQuotient x,z.2) := Prod.ext hx.symm rfl
  rw [hz,derivative_at_quotient,iteratedFDeriv_two_apply]
  change p.val.2.2.1 (torusQuotient x) a b z.2=(fderiv ℝ (fderiv ℝ (fieldLift p.val.1)) x) a b z.2
  rw [compatible_second_fderiv p.property]

def fieldAdvection (R : ℝ) (g : C(SpatialTorus,RealPosition→L[ℝ]V0 R)) : Distribution R :=
  ⟨fun z => g z.1 (velocity R z.2) z.2,by
    have hv : Continuous (fun z : Phase R => velocity R z.2) := by
      unfold velocity
      apply continuous_pi
      intro j
      fun_prop
    exact Continuous.eval ((g.continuous.comp continuous_fst).clm_apply hv) continuous_snd⟩

theorem field_transport_hasDerivAt (R : ℝ) (f : C(SpatialTorus,V0 R))
    (g : C(SpatialTorus,RealPosition→L[ℝ]V0 R)) (hfg : (f,g)∈fieldDerivativeGraph) (t : ℝ) :
    HasDerivAt (fun τ => transport R (-τ) (ContinuousMap.uncurry f))
      (transport R (-t) (fieldAdvection R g)) t := by
  apply hasDerivAt_of_evaluations (D := fun τ => transport R (-τ) (fieldAdvection R g))
  · exact ((transport_strong_continuous R (fieldAdvection R g)).comp continuous_neg).continuousAt
  · intro s z
    obtain ⟨a,ha⟩ := torusQuotient_surjective z.1
    have hz : z=(torusQuotient a,z.2) := Prod.ext ha.symm rfl
    rw [hz]
    have hx : HasDerivAt (fun τ : ℝ => a+τ • velocity R z.2) (velocity R z.2) s := by
      simpa only [one_smul] using (hasDerivAt_id s).smul_const (velocity R z.2) |>.const_add a
    have hp := (hfg (a+s • velocity R z.2)).comp_hasDerivAt s hx
    have h := (ContinuousMap.evalCLM (R := ℝ) z.2).hasFDerivAt.comp_hasDerivAt s hp
    have he : (fun τ => transport R (-τ) (ContinuousMap.uncurry f) (torusQuotient a,z.2))=
        fun τ => fieldLift f (a+τ • velocity R z.2) z.2 := by
      funext τ
      rw [transport_apply,characteristic_lift]
      rfl
    rw [he]
    convert h using 1
    rw [transport_apply,characteristic_lift]
    rfl

def firstDerivativeField (R : ℝ) (p : Space R) (a : RealPosition) :
    C(SpatialTorus,RealPosition→L[ℝ]V0 R) :=
  ⟨fun X => (ContinuousLinearMap.apply ℝ (V0 R) a).comp (p.val.2.2.1 X),by fun_prop⟩

def secondDerivativeField (R : ℝ) (p : Space R) (a b : RealPosition) :
    C(SpatialTorus,RealPosition→L[ℝ]V0 R) :=
  ⟨fun X => ((ContinuousLinearMap.apply ℝ (V0 R) b).comp
    (ContinuousLinearMap.apply ℝ (V1 R) a)).comp (p.val.2.2.2 X),by fun_prop⟩

theorem firstField_graph (R : ℝ) (p : Space R) (a : RealPosition) :
    (firstField R p a,firstDerivativeField R p a)∈fieldDerivativeGraph := by
  intro x
  exact (ContinuousLinearMap.apply ℝ (V0 R) a).hasFDerivAt.comp x (p.property.2.1 x)

theorem secondField_graph (R : ℝ) (p : Space R) (a b : RealPosition) :
    (secondField R p a b,secondDerivativeField R p a b)∈fieldDerivativeGraph := by
  intro x
  exact ((ContinuousLinearMap.apply ℝ (V0 R) b).comp
    (ContinuousLinearMap.apply ℝ (V1 R) a)).hasFDerivAt.comp x (p.property.2.2 x)

theorem first_transport_hasDerivAt (R : ℝ) (p : Space R) (a : RealPosition) (t : ℝ) :
    HasDerivAt (fun τ => transport R (-τ) (spatialDerivative R 1 (by omega) ![a] p))
      (transport R (-t) (fieldAdvection R (firstDerivativeField R p a))) t := by
  rw [←firstField_actual]
  exact field_transport_hasDerivAt R _ _ (firstField_graph R p a) t

theorem second_transport_hasDerivAt (R : ℝ) (p : Space R) (a b : RealPosition) (t : ℝ) :
    HasDerivAt (fun τ => transport R (-τ) (spatialDerivative R 2 (by omega) ![a,b] p))
      (transport R (-t) (fieldAdvection R (secondDerivativeField R p a b))) t := by
  rw [←secondField_actual]
  exact field_transport_hasDerivAt R _ _ (secondField_graph R p a b) t

section LinearReadout
variable {R : ℝ} (L : Space R→L[ℝ]Distribution R) (A : Space R→Distribution R)
  (hL : ∀ t p,L (JetTransport.map R t p)=transport R t (L p))
  (hA : ∀ p t,HasDerivAt (fun τ => transport R (-τ) (L p))
    (transport R (-t) (A p)) t)
include hL hA

theorem advected_readout_commutes (t : ℝ) (p : Space R) :
    A (JetTransport.map R t p)=transport R t (A p) := by
  have h1 := hA (JetTransport.map R t p) 0
  have h2 := (transportCLM R t).hasFDerivAt.comp_hasDerivAt 0 (hA p 0)
  simp only [neg_zero,transport_zero] at h1 h2
  have he : (fun s => transport R (-s) (L (JetTransport.map R t p)))=
      fun s => transportCLM R t (transport R (-s) (L p)) := by
    funext s
    rw [hL]
    change transport R (-s) (transport R t (L p))=transport R t (transport R (-s) (L p))
    rw [transport_add_time,transport_add_time,add_comm]
  rw [he] at h1
  exact h1.unique h2

theorem physical_linear_readout_derivative {T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (g : ℝ→Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t∈Icc 0 T,g t=p₀+∫ s in (0:ℝ)..t,JetKineticField.field R hR c s (g s))
    {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => L (JetTransport.map R τ (g τ)))
      (c • L (JetCollision.collision R hR (JetTransport.map R t (g t)))-
        A (JetTransport.map R t (g t))) (Icc 0 T) t := by
  have hg' := L.hasFDerivAt.comp_hasDerivWithinAt t
    (JetMildEquation.moving_frame_hasDerivWithinAt hR hT c p₀ g hg he t ht)
  have hf := (hA (g t) (-t)).scomp t (hasDerivAt_id t).neg
  have hf' : HasDerivAt (fun τ => transport R τ (L (g t)))
      (-(transport R t (A (g t)))) t := by simpa [Function.comp_def] using hf
  have h := strong_family_hasDerivWithinAt (fun τ => transportCLM R τ)
    (TransportDuhamel.transport_joint_continuous R) hg' hf'.hasDerivWithinAt
  change HasDerivWithinAt (fun τ => transport R τ (L (g τ)))
    (transport R t (L (JetKineticField.field R hR c t (g t)))+
      -(transport R t (A (g t)))) (Icc 0 T) t at h
  simp only [JetKineticField.field,map_smul,hL,transport_smul,transport_add_time,
    add_neg_cancel,transport_zero,←advected_readout_commutes L A hL hA,←sub_eq_add_neg] at h
  simpa only [hL] using h

theorem original_mild_linear_readout_derivative {T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => L (p τ))
      (c • L (JetCollision.collision R hR (p t))-A (p t)) (Icc 0 T) t := by
  have h := physical_linear_readout_derivative L A hL hA hR hT c p₀
    (JetAmplitudeBounds.toFrame R p) (JetAmplitudeBounds.toFrame_continuousOn hp)
    (JetAmplitudeBounds.actual_mild_to_moving_frame hR c p₀ p hp he) ht
  simpa only [JetAmplitudeBounds.toFrame,JetTransport.map_add_time,add_neg_cancel,
    JetTransport.map_zero_time] using h
end LinearReadout

theorem original_mild_first_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => spatialDerivative R 1 (by omega) ![a] (p τ))
      (c • spatialDerivative R 1 (by omega) ![a] (JetCollision.collision R hR (p t))-
        fieldAdvection R (firstDerivativeField R (p t) a)) (Icc 0 T) t :=
  original_mild_linear_readout_derivative (spatialDerivative R 1 (by omega) ![a])
    (fun q => fieldAdvection R (firstDerivativeField R q a))
    (fun t q => spatialDerivative_transport R t 1 (by omega) ![a] q)
    (fun q t => first_transport_hasDerivAt R q a t) hR hT c p₀ p hp he ht

theorem original_mild_second_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => spatialDerivative R 2 (by omega) ![a,b] (p τ))
      (c • spatialDerivative R 2 (by omega) ![a,b] (JetCollision.collision R hR (p t))-
        fieldAdvection R (secondDerivativeField R (p t) a b)) (Icc 0 T) t :=
  original_mild_linear_readout_derivative (spatialDerivative R 2 (by omega) ![a,b])
    (fun q => fieldAdvection R (secondDerivativeField R q a b))
    (fun t q => spatialDerivative_transport R t 2 (by omega) ![a,b] q)
    (fun q t => second_transport_hasDerivAt R q a b t) hR hT c p₀ p hp he ht

theorem original_mild_first_moment_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (θ : Thermodynamics.Parameter) (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => ContinuousCollisionMoments.spatialMoment R θ
      (spatialDerivative R 1 (by omega) ![a] (p τ)))
      (-ContinuousCollisionMoments.spatialMoment R θ
        (fieldAdvection R (firstDerivativeField R (p t) a))) (Icc 0 T) t := by
  have h := (ContinuousCollisionMoments.spatialMoment R θ).hasFDerivAt.comp_hasDerivWithinAt t
    (original_mild_first_derivative hR hT c p₀ p hp he a ht)
  simpa only [map_sub,map_smul,ContinuousCollisionMoments.spatial_derivative_collision_five_moments hR,
    smul_zero,zero_sub] using h

theorem original_mild_second_moment_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (θ : Thermodynamics.Parameter) (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => ContinuousCollisionMoments.spatialMoment R θ
      (spatialDerivative R 2 (by omega) ![a,b] (p τ)))
      (-ContinuousCollisionMoments.spatialMoment R θ
        (fieldAdvection R (secondDerivativeField R (p t) a b))) (Icc 0 T) t := by
  have h := (ContinuousCollisionMoments.spatialMoment R θ).hasFDerivAt.comp_hasDerivWithinAt t
    (original_mild_second_derivative hR hT c p₀ p hp he a b ht)
  simpa only [map_sub,map_smul,ContinuousCollisionMoments.spatial_derivative_collision_five_moments hR,
    smul_zero,zero_sub] using h

end
end Resonance.LowSpatialMaterialDerivative

#check Resonance.LowSpatialMaterialDerivative.derivative_at_quotient
#check Resonance.LowSpatialMaterialDerivative.firstField_actual
#check Resonance.LowSpatialMaterialDerivative.secondField_actual
#check Resonance.LowSpatialMaterialDerivative.field_transport_hasDerivAt
#check Resonance.LowSpatialMaterialDerivative.firstField_graph
#check Resonance.LowSpatialMaterialDerivative.secondField_graph
#check Resonance.LowSpatialMaterialDerivative.first_transport_hasDerivAt
#check Resonance.LowSpatialMaterialDerivative.second_transport_hasDerivAt
#check Resonance.LowSpatialMaterialDerivative.advected_readout_commutes
#check Resonance.LowSpatialMaterialDerivative.physical_linear_readout_derivative
#check Resonance.LowSpatialMaterialDerivative.original_mild_linear_readout_derivative
#check Resonance.LowSpatialMaterialDerivative.original_mild_first_derivative
#check Resonance.LowSpatialMaterialDerivative.original_mild_second_derivative
#check Resonance.LowSpatialMaterialDerivative.original_mild_first_moment_derivative
#check Resonance.LowSpatialMaterialDerivative.original_mild_second_moment_derivative
#print axioms Resonance.LowSpatialMaterialDerivative.derivative_at_quotient
#print axioms Resonance.LowSpatialMaterialDerivative.firstField_actual
#print axioms Resonance.LowSpatialMaterialDerivative.secondField_actual
#print axioms Resonance.LowSpatialMaterialDerivative.field_transport_hasDerivAt
#print axioms Resonance.LowSpatialMaterialDerivative.firstField_graph
#print axioms Resonance.LowSpatialMaterialDerivative.secondField_graph
#print axioms Resonance.LowSpatialMaterialDerivative.first_transport_hasDerivAt
#print axioms Resonance.LowSpatialMaterialDerivative.second_transport_hasDerivAt
#print axioms Resonance.LowSpatialMaterialDerivative.advected_readout_commutes
#print axioms Resonance.LowSpatialMaterialDerivative.physical_linear_readout_derivative
#print axioms Resonance.LowSpatialMaterialDerivative.original_mild_linear_readout_derivative
#print axioms Resonance.LowSpatialMaterialDerivative.original_mild_first_derivative
#print axioms Resonance.LowSpatialMaterialDerivative.original_mild_second_derivative
#print axioms Resonance.LowSpatialMaterialDerivative.original_mild_first_moment_derivative
#print axioms Resonance.LowSpatialMaterialDerivative.original_mild_second_moment_derivative
