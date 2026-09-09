import Resonance.ActualCoframeBMaterial
import Resonance.JetRelativeEnergy

/-! The exact relative-coframe equation of the original kinetic trajectory.
Reference paths and G have actual compatible moving-frame derivatives; their
residual is defined from the same full collision, without an error estimate. -/
open Set Function MeasureTheory
namespace Resonance.RelativeCoframeEvolution
noncomputable section
open FreeTransport JetCollision SpatialChainRule JetEnergy ActualMatchedMoments
open ThermodynamicChart ActualCoframeWeight ActualCoframeLowTime RelativeCoframeJets
open ActualCoframeBMaterial PhaseEnergy
set_option maxHeartbeats 1600000

inductive Index
  | zero
  | first (i : Fin 3)
  | second (i j : Fin 3)
  | third (i j k : Fin 3)
  deriving DecidableEq, Fintype

theorem index_card : Fintype.card Index=40 := by decide

def direction (i : Fin 3) : RealPosition := Pi.single i 1

def order : Index→ℕ
  | .zero => 0
  | .first _ => 1
  | .second _ _ => 2
  | .third _ _ _ => 3

def directions : (a : Index)→Fin (order a)→RealPosition
  | .zero => ![]
  | .first i => ![direction i]
  | .second i j => ![direction i,direction j]
  | .third i j k => ![direction i,direction j,direction k]

theorem order_le (a : Index) : order a≤3 := by cases a <;> simp [order]

def derivative (R : ℝ) (a : Index) : Space R→L[ℝ]Distribution R :=
  spatialDerivative R (order a) (order_le a) (directions a)

theorem derivative_transport (R t : ℝ) (a : Index) (p : Space R) :
    derivative R a (JetTransport.map R t p)=transport R t (derivative R a p) :=
  spatialDerivative_transport R t (order a) (order_le a) (directions a) p

section Actual
variable (R T : ℝ) (hR : 0<R) (p : ℝ→Space R)
  (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
  (c : ℝ)

def BMoving (a : Index) (t : ℝ) : Distribution R :=
  actualBMoving R T hR p himage (order a) (order_le a) (directions a) t

def BRate (a : Index) (t : ℝ) : Distribution R := match a with
  | .zero => 0
  | .first _ => 0
  | .second i j => BSecondMovingRate R T hR p himage c (direction i) (direction j) t
  | .third i j k => BThirdMovingRate R T hR p himage c (direction i) (direction j) (direction k) t

def logMaterial (t : ℝ) : Distribution R :=
  -(NMoving R T hR p himage t*qMovingRate R T hR p himage c t)

/-- G and the reciprocal reference are read in the same characteristic frame. -/
def HMoving (G b : ℝ→Space R) (a : Index) (t : ℝ) : Distribution R :=
  qMoving R T hR p himage t*derivative R a (JetAmplitudeBounds.toFrame R p t-G t)+
    NMoving R T hR p himage t*derivative R a (b t)-BMoving R T hR p himage a t

def HPhysical (G b : ℝ→Space R) (a : Index) (t : ℝ) : Distribution R := by
  classical
  exact if ht : t∈Icc 0 T then relativeH (p t) (JetTransport.map R t (G t))
    (actualQ R T hR p himage t) (JetTransport.map R t (b t))
    (fun z => ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht z))
    (order a) (order_le a) (directions a) else 0

theorem HMoving_physical (G b : ℝ→Space R) (a : Index) {t : ℝ} (ht : t∈Icc 0 T) :
    HMoving R T hR p himage G b a t=transport R (-t) (HPhysical R T hR p himage G b a t) := by
  have hs (u v : Distribution R) : transport R (-t) (u-v)=transport R (-t) u-transport R (-t) v :=
    (transportCLM R (-t)).map_sub u v
  have hjs (u v : Space R) : JetTransport.map R (-t) (u-v)=JetTransport.map R (-t) u-JetTransport.map R (-t) v :=
    (JetTransport.operator R (-t)).map_sub u v
  rw [HPhysical,dif_pos ht,H_identity]
  simp only [hs,transport_add,PhaseEnergy.transport_mul]
  change HMoving R T hR p himage G b a t=
    transport R (-t) (readback (actualQ R T hR p himage t))*
      transport R (-t) (derivative R a (p t-JetTransport.map R t (G t)))+
    transport R (-t) (Nfield _ _)*transport R (-t) (derivative R a (JetTransport.map R t (b t)))-_
  rw [←derivative_transport,←derivative_transport,JetTransport.map_add_time,neg_add_cancel,
    JetTransport.map_zero_time]
  simp only [HMoving,BMoving,actualBMoving,dif_pos ht,NMoving_actual R T hR p himage ht,
    hjs,map_sub,JetTransport.map_add_time,neg_add_cancel,JetTransport.map_zero_time,
    JetAmplitudeBounds.toFrame,qMoving]

theorem HMoving_energy_physical (G b : ℝ→Space R) (a : Index) {t : ℝ} (ht : t∈Icc 0 T) :
    quadratic R 1 (HMoving R T hR p himage G b a t)=
      quadratic R 1 (HPhysical R T hR p himage G b a t) := by
  rw [HMoving_physical R T hR p himage G b a ht]
  have h := quadratic_transport R (-t) (1:Distribution R) (HPhysical R T hR p himage G b a t)
  exact h

def collisionMoving (f : Space R) (t : ℝ) : Space R :=
  JetTransport.map R (-t) (JetCollision.collision R hR.le f)

/-- Exactly the material residual of Nbar+G, evaluated on that same full
approximate state. No size bound is included in its definition. -/
def appResidualMoving (Nbar G : ℝ→Space R) (Nbar' G' : Space R) (t : ℝ) : Space R :=
  Nbar'+G'-c • collisionMoving R hR (JetTransport.map R t (Nbar t+G t)) t

theorem appResidual_actual_material (Nbar G : ℝ→Space R) (Nbar' G' : Space R)
    {s : Set ℝ} {t : ℝ} (hN : HasDerivWithinAt Nbar Nbar' s t)
    (hG : HasDerivWithinAt G G' s t) :
    HasDerivWithinAt (fun τ => Nbar τ+G τ)
      (c • collisionMoving R hR (JetTransport.map R t (Nbar t+G t)) t+
        appResidualMoving R hR c Nbar G Nbar' G' t) s t := by
  convert hN.add hG using 1
  simp only [appResidualMoving]
  abel

def sourceR (b : ℝ→Space R) (b' Nbar' : Space R) (a : Index) (t : ℝ) : Distribution R :=
  NMoving R T hR p himage t*derivative R a b'+
    (2:ℝ) • (logMaterial R T hR p himage c t*NMoving R T hR p himage t*derivative R a (b t))-
    (BRate R T hR p himage c a t+logMaterial R T hR p himage c t*BMoving R T hR p himage a t)+
    qMoving R T hR p himage t*derivative R a Nbar'

def equationRate (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R) (a : Index) (t : ℝ) : Distribution R :=
  c • (qMoving R T hR p himage t*derivative R a
    (collisionMoving R hR (p t) t-collisionMoving R hR (JetTransport.map R t (Nbar t+G t)) t))-
    logMaterial R T hR p himage c t*HMoving R T hR p himage G b a t+
    sourceR R T hR p himage c b b' Nbar' a t-
    qMoving R T hR p himage t*derivative R a (appResidualMoving R hR c Nbar G Nbar' G' t)

theorem inverse_product {t : ℝ} (ht : t∈Icc 0 T) :
    qMoving R T hR p himage t*NMoving R T hR p himage t=1 := by
  exact Ring.mul_inverse_cancel _ ((ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    (qMoving_nonzero R T hR p himage ht))

theorem qRate_logMaterial {t : ℝ} (ht : t∈Icc 0 T) :
    qMovingRate R T hR p himage c t=
      -(logMaterial R T hR p himage c t*qMoving R T hR p himage t) := by
  have h := inverse_product R T hR p himage ht
  unfold logMaterial
  calc
    _ = (qMoving R T hR p himage t*NMoving R T hR p himage t)*qMovingRate R T hR p himage c t := by rw [h,one_mul]
    _ = _ := by ring

theorem NRate_logMaterial (t : ℝ) : NMovingRate R T hR p himage c t=
    logMaterial R T hR p himage c t*NMoving R T hR p himage t := by
  unfold NMovingRate logMaterial
  ring

theorem logMaterial_actual_value {t : ℝ} (ht : t∈Icc 0 T)
    (x : RealPosition) (k : MomentumDomain R) :
    transport R t (logMaterial R T hR p himage c t) (torusQuotient x,k)=
      -WeightedJointMeasure.profile (matchedValue R hR (readback (p t)) (torusQuotient x)) k*
        WeightedPhysicalForm.reciprocalProfile (matchedMaterialParameter R hR (p t) x k) k := by
  have hn := NMoving_actual R T hR p himage ht
  have hneg (f : Distribution R) : transport R t (-f) = -transport R t f :=
    (transportCLM R t).map_neg f
  simp only [logMaterial,hneg,transport_mul,hn,qMovingRate,transport_add_time,
    add_neg_cancel,transport_zero,ContinuousMap.neg_apply,ContinuousMap.mul_apply,
    ContinuousMap.add_apply,actualQ]
  rw [coframe_material_rate R hR (Icc 0 T) c p himage ht x k]
  simp only [Nfield,JetReciprocal.inverseJet_readback,
    coframeJet_actual_value R hR (Icc 0 T) p himage ht,inv_inv,neg_mul]

def etaPhysical (G : ℝ→Space R) (a : Index) (t : ℝ) : Distribution R := by
  classical
  exact if ht : t∈Icc 0 T then eta (p t) (JetTransport.map R t (G t))
    (actualQ R T hR p himage t)
    (fun z => ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht z))
    (order a) (order_le a) (directions a) else 0

theorem HPhysical_collision_replacement (G b : ℝ→Space R) (fapp : Space R)
    (a : Index) {t : ℝ} (ht : t∈Icc 0 T)
    (θbar : C(SpatialTorus,Thermodynamics.Parameter))
    (hθbar : ContDiff ℝ 3 (SpatialJetSpace.fieldLift θbar))
    (hbar : JetTransport.map R t (b t)=ParameterSpatialJets.denominatorJet R θbar hθbar) :
    integralCLM R (HPhysical R T hR p himage G b a t*
      (readback (actualQ R T hR p himage t)*derivative R a
        (JetCollision.collision R hR.le (p t)-JetCollision.collision R hR.le fapp)))=
    integralCLM R (etaPhysical R T hR p himage G a t*
      (readback (actualQ R T hR p himage t)*derivative R a
        (JetCollision.collision R hR.le (p t)-JetCollision.collision R hR.le fapp))) := by
  rw [HPhysical,dif_pos ht,etaPhysical,dif_pos ht,hbar]
  exact H_full_collision_difference_pairing hR.le (p t) (JetTransport.map R t (G t)) fapp
    (MatchedContinuousTime.parameterPath R hR (Icc 0 T) (fun τ => readback (p τ)) himage t) θbar
    (actual_parameterPath_contDiff R hR (Icc 0 T) p himage t) hθbar
    (fun z => ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht z))
    (order a) (order_le a) (directions a)

theorem moving_collision_pairing (G b : ℝ→Space R) (fapp : Space R)
    (a : Index) {t : ℝ} (ht : t∈Icc 0 T) :
    integralCLM R (HMoving R T hR p himage G b a t*
      (qMoving R T hR p himage t*derivative R a
        (collisionMoving R hR (p t) t-collisionMoving R hR fapp t)))=
    integralCLM R (HPhysical R T hR p himage G b a t*
      (readback (actualQ R T hR p himage t)*derivative R a
        (JetCollision.collision R hR.le (p t)-JetCollision.collision R hR.le fapp))) := by
  have hjs (u v : Space R) : JetTransport.map R (-t) (u-v)=JetTransport.map R (-t) u-JetTransport.map R (-t) v :=
    (JetTransport.operator R (-t)).map_sub u v
  rw [collisionMoving,collisionMoving,←hjs,derivative_transport,HMoving_physical R T hR p himage G b a ht]
  exact triple_transport R (-t) _ _ _

theorem full_same_phase_collision_orthogonality (G b : ℝ→Space R) (fapp : Space R)
    (a : Index) {t : ℝ} (ht : t∈Icc 0 T)
    (θbar : C(SpatialTorus,Thermodynamics.Parameter))
    (hθbar : ContDiff ℝ 3 (SpatialJetSpace.fieldLift θbar))
    (hbar : JetTransport.map R t (b t)=ParameterSpatialJets.denominatorJet R θbar hθbar) :
    integralCLM R (HMoving R T hR p himage G b a t*
      (qMoving R T hR p himage t*derivative R a
        (collisionMoving R hR (p t) t-collisionMoving R hR fapp t)))=
    integralCLM R (etaPhysical R T hR p himage G a t*
      (readback (actualQ R T hR p himage t)*derivative R a
        (JetCollision.collision R hR.le (p t)-JetCollision.collision R hR.le fapp))) := by
  rw [moving_collision_pairing R T hR p himage G b fapp a ht]
  exact HPhysical_collision_replacement R T hR p himage G b fapp a ht θbar hθbar hbar

def coframeEnergy (G b : ℝ→Space R) (ω : ℕ→ℝ) (t : ℝ) : ℝ :=
  ∑ a : Index,ω (order a)*quadratic R 1 (HPhysical R T hR p himage G b a t)

def coframeEnergyRate (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R)
    (ω : ℕ→ℝ) (t : ℝ) : ℝ :=
  ∑ a : Index,ω (order a)*integralCLM R
    (HMoving R T hR p himage G b a t*equationRate R T hR p himage c Nbar G b Nbar' G' b' a t)

/-- Every collision, metric, reference and residual contribution remains in
the same phase integral. -/
theorem equation_energy_expansion (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R)
    (a : Index) (t : ℝ) :
    integralCLM R (HMoving R T hR p himage G b a t*
      equationRate R T hR p himage c Nbar G b Nbar' G' b' a t)=
    c*integralCLM R (HMoving R T hR p himage G b a t*
      (qMoving R T hR p himage t*derivative R a
        (collisionMoving R hR (p t) t-collisionMoving R hR (JetTransport.map R t (Nbar t+G t)) t)))-
    integralCLM R (logMaterial R T hR p himage c t*
      (HMoving R T hR p himage G b a t*HMoving R T hR p himage G b a t))+
    integralCLM R (HMoving R T hR p himage G b a t*sourceR R T hR p himage c b b' Nbar' a t)-
    integralCLM R (HMoving R T hR p himage G b a t*
      (qMoving R T hR p himage t*derivative R a (appResidualMoving R hR c Nbar G Nbar' G' t))) := by
  simp only [equationRate,mul_sub,mul_add,mul_smul_comm,map_sub,map_add,map_smul,
    smul_eq_mul,mul_left_comm]

def resolvedEnergyRate (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R)
    (ω : ℕ→ℝ) (t : ℝ) : ℝ :=
  ∑ a : Index,ω (order a)*(
    c*integralCLM R (etaPhysical R T hR p himage G a t*
      (readback (actualQ R T hR p himage t)*derivative R a
        (JetCollision.collision R hR.le (p t)-
          JetCollision.collision R hR.le (JetTransport.map R t (Nbar t+G t)))))-
    integralCLM R (logMaterial R T hR p himage c t*
      (HMoving R T hR p himage G b a t*HMoving R T hR p himage G b a t))+
    integralCLM R (HMoving R T hR p himage G b a t*sourceR R T hR p himage c b b' Nbar' a t)-
    integralCLM R (HMoving R T hR p himage G b a t*
      (qMoving R T hR p himage t*derivative R a (appResidualMoving R hR c Nbar G Nbar' G' t))))

theorem coframeEnergyRate_resolved (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R)
    (ω : ℕ→ℝ) {t : ℝ} (ht : t∈Icc 0 T)
    (θbar : C(SpatialTorus,Thermodynamics.Parameter))
    (hθbar : ContDiff ℝ 3 (SpatialJetSpace.fieldLift θbar))
    (hbar : JetTransport.map R t (b t)=ParameterSpatialJets.denominatorJet R θbar hθbar) :
    coframeEnergyRate R T hR p himage c Nbar G b Nbar' G' b' ω t=
      resolvedEnergyRate R T hR p himage c Nbar G b Nbar' G' b' ω t := by
  unfold coframeEnergyRate resolvedEnergyRate
  apply Finset.sum_congr rfl
  intro a _
  rw [equation_energy_expansion,
    full_same_phase_collision_orthogonality R T hR p himage G b
      (JetTransport.map R t (Nbar t+G t)) a ht θbar hθbar hbar]

variable (hT : 0≤T) (p₀ : Space R) (hp : ContinuousOn p (Icc 0 T))
  (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
    ∫ s in (0:ℝ)..t,c • transport R (t-s)
      (SpatialCollision.collision R hR.le (readback (p s))))
include hp he hT

theorem logMaterial_is_material_log_derivative (x : RealPosition) (k : MomentumDomain R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    ∃ Bt : ℝ,
      HasDerivWithinAt (fun τ => Real.log (WeightedJointMeasure.profile
        (matchedValue R hR (readback (p τ)) (torusQuotient x)) k)) Bt (Icc 0 T) t ∧
      Bt+fderiv ℝ (fun y => Real.log (WeightedJointMeasure.profile
          (matchedValue R hR (readback (p t)) (torusQuotient y)) k)) x
          (TransportMaterialDerivative.velocity R k)=
        transport R t (logMaterial R T hR p himage c t) (torusQuotient x,k) := by
  rw [logMaterial_actual_value R T hR p himage c ht x k]
  exact actual_matched_material_log_derivative hR hT c p₀ p hp he x ht
    (himage t ht (torusQuotient x)) k

theorem BMoving_hasDerivWithinAt (a : Index) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (BMoving R T hR p himage a) (BRate R T hR p himage c a t) (Icc 0 T) t := by
  cases a with
  | zero => exact actualBMoving_zero_derivative R T hR p himage ![] ht
  | first i => exact actualBMoving_first_derivative R T hR p himage (direction i) ht
  | second i j => exact actualBMoving_second_derivative R T hR p himage c hT p₀ hp he (direction i) (direction j) ht
  | third i j k => exact actualBMoving_third_derivative R T hR p himage c hT p₀ hp he (direction i) (direction j) (direction k) ht

theorem original_mild_H_equation (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R)
    {t : ℝ} (ht : t∈Icc 0 T)
    (hG : HasDerivWithinAt G G' (Icc 0 T) t)
    (hb : HasDerivWithinAt b b' (Icc 0 T) t)
    (a : Index) :
    HasDerivWithinAt (HMoving R T hR p himage G b a)
      (equationRate R T hR p himage c Nbar G b Nbar' G' b' a t) (Icc 0 T) t := by
  have hg := JetMildEquation.moving_frame_hasDerivWithinAt hR.le hT c p₀
    (JetAmplitudeBounds.toFrame R p) (JetAmplitudeBounds.toFrame_continuousOn hp)
    (JetAmplitudeBounds.actual_mild_to_moving_frame hR.le c p₀ p hp he) t ht
  have hD := (derivative R a).hasFDerivAt.comp_hasDerivWithinAt t (hg.sub hG)
  have hQ := actualQ_material R T hR p himage hT c p₀ hp he ht
  have hN := NMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he ht
  have hDb := (derivative R a).hasFDerivAt.comp_hasDerivWithinAt t hb
  have h := ((hQ.mul hD).add (hN.mul hDb)).sub
    (BMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he a ht)
  have hfield : JetKineticField.field R hR.le c t (JetAmplitudeBounds.toFrame R p t)=
      c • collisionMoving R hR (p t) t := by
    simp only [JetKineticField.field,JetAmplitudeBounds.toFrame,JetTransport.map_add_time,
      add_neg_cancel,JetTransport.map_zero_time]
    rfl
  change HasDerivWithinAt (HMoving R T hR p himage G b a)
    (qMovingRate R T hR p himage c t*derivative R a
      (JetAmplitudeBounds.toFrame R p t-G t)+
      qMoving R T hR p himage t*derivative R a
        (JetKineticField.field R hR.le c t (JetAmplitudeBounds.toFrame R p t)-G')+
      (NMovingRate R T hR p himage c t*derivative R a (b t)+
        NMoving R T hR p himage t*derivative R a b')-
      BRate R T hR p himage c a t) (Icc 0 T) t at h
  rw [hfield,qRate_logMaterial R T hR p himage c ht,NRate_logMaterial] at h
  apply h.congr_deriv
  simp only [equationRate,HMoving,sourceR,appResidualMoving,map_sub,map_add,map_smul]
  ext z
  simp only [ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.mul_apply,
    ContinuousMap.neg_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring

theorem original_mild_H_energy (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R)
    {t : ℝ} (ht : t∈Icc 0 T)
    (hG : HasDerivWithinAt G G' (Icc 0 T) t)
    (hb : HasDerivWithinAt b b' (Icc 0 T) t) (ω : ℕ→ℝ) :
    HasDerivWithinAt (coframeEnergy R T hR p himage G b ω)
      (coframeEnergyRate R T hR p himage c Nbar G b Nbar' G' b' ω t) (Icc 0 T) t := by
  have ha (a : Index) := quadratic_hasDerivWithinAt R
    (hasDerivWithinAt_const t (Icc 0 T) (1:Distribution R))
    (original_mild_H_equation R T hR p himage c hT p₀ hp he Nbar G b Nbar' G' b' ht hG hb a)
  simp only [zero_mul,map_zero,mul_zero,zero_add,one_mul] at ha
  have h := HasDerivWithinAt.sum (u := Finset.univ) (fun a _ => (ha a).const_mul (ω (order a)))
  exact h.congr_of_mem (fun τ hτ => by
    unfold coframeEnergy
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [HMoving_energy_physical R T hR p himage G b a hτ]) ht

/-- The physical H³ energy has this exact full-collision rate. The only
reference-field input is its actual compatible denominator jet; G carries
its genuine material derivative and the displayed, unestimated residual. -/
theorem original_mild_H_energy_resolved (Nbar G b : ℝ→Space R) (Nbar' G' b' : Space R)
    {t : ℝ} (ht : t∈Icc 0 T)
    (hG : HasDerivWithinAt G G' (Icc 0 T) t)
    (hb : HasDerivWithinAt b b' (Icc 0 T) t) (ω : ℕ→ℝ)
    (θbar : C(SpatialTorus,Thermodynamics.Parameter))
    (hθbar : ContDiff ℝ 3 (SpatialJetSpace.fieldLift θbar))
    (hbar : JetTransport.map R t (b t)=ParameterSpatialJets.denominatorJet R θbar hθbar) :
    HasDerivWithinAt (coframeEnergy R T hR p himage G b ω)
      (resolvedEnergyRate R T hR p himage c Nbar G b Nbar' G' b' ω t) (Icc 0 T) t := by
  rw [←coframeEnergyRate_resolved R T hR p himage c Nbar G b Nbar' G' b' ω ht θbar hθbar hbar]
  exact original_mild_H_energy R T hR p himage c hT p₀ hp he Nbar G b Nbar' G' b' ht hG hb ω
end Actual

end
end Resonance.RelativeCoframeEvolution

#check Resonance.RelativeCoframeEvolution.index_card
#check Resonance.RelativeCoframeEvolution.order_le
#check Resonance.RelativeCoframeEvolution.derivative_transport
#check Resonance.RelativeCoframeEvolution.HMoving_physical
#check Resonance.RelativeCoframeEvolution.HMoving_energy_physical
#check Resonance.RelativeCoframeEvolution.appResidual_actual_material
#check Resonance.RelativeCoframeEvolution.inverse_product
#check Resonance.RelativeCoframeEvolution.qRate_logMaterial
#check Resonance.RelativeCoframeEvolution.NRate_logMaterial
#check Resonance.RelativeCoframeEvolution.logMaterial_actual_value
#check Resonance.RelativeCoframeEvolution.HPhysical_collision_replacement
#check Resonance.RelativeCoframeEvolution.moving_collision_pairing
#check Resonance.RelativeCoframeEvolution.full_same_phase_collision_orthogonality
#check Resonance.RelativeCoframeEvolution.equation_energy_expansion
#check Resonance.RelativeCoframeEvolution.coframeEnergyRate_resolved
#check Resonance.RelativeCoframeEvolution.logMaterial_is_material_log_derivative
#check Resonance.RelativeCoframeEvolution.BMoving_hasDerivWithinAt
#check Resonance.RelativeCoframeEvolution.original_mild_H_equation
#check Resonance.RelativeCoframeEvolution.original_mild_H_energy
#check Resonance.RelativeCoframeEvolution.original_mild_H_energy_resolved
#print axioms Resonance.RelativeCoframeEvolution.index_card
#print axioms Resonance.RelativeCoframeEvolution.order_le
#print axioms Resonance.RelativeCoframeEvolution.derivative_transport
#print axioms Resonance.RelativeCoframeEvolution.HMoving_physical
#print axioms Resonance.RelativeCoframeEvolution.HMoving_energy_physical
#print axioms Resonance.RelativeCoframeEvolution.appResidual_actual_material
#print axioms Resonance.RelativeCoframeEvolution.inverse_product
#print axioms Resonance.RelativeCoframeEvolution.qRate_logMaterial
#print axioms Resonance.RelativeCoframeEvolution.NRate_logMaterial
#print axioms Resonance.RelativeCoframeEvolution.logMaterial_actual_value
#print axioms Resonance.RelativeCoframeEvolution.HPhysical_collision_replacement
#print axioms Resonance.RelativeCoframeEvolution.moving_collision_pairing
#print axioms Resonance.RelativeCoframeEvolution.full_same_phase_collision_orthogonality
#print axioms Resonance.RelativeCoframeEvolution.equation_energy_expansion
#print axioms Resonance.RelativeCoframeEvolution.coframeEnergyRate_resolved
#print axioms Resonance.RelativeCoframeEvolution.logMaterial_is_material_log_derivative
#print axioms Resonance.RelativeCoframeEvolution.BMoving_hasDerivWithinAt
#print axioms Resonance.RelativeCoframeEvolution.original_mild_H_equation
#print axioms Resonance.RelativeCoframeEvolution.original_mild_H_energy
#print axioms Resonance.RelativeCoframeEvolution.original_mild_H_energy_resolved
