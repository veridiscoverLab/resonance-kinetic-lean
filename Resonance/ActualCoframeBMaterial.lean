import Resonance.ActualCoframeLowTime

/-! The actual time-dependent coframe correction B up to order three.
Its material differentiation uses precisely q, Dq, D²q and their proved
strong time derivatives, retaining every metric and ordered product term. -/
open Set Function
namespace Resonance.ActualCoframeBMaterial
noncomputable section
open FreeTransport JetCollision SpatialChainRule JetEnergy ActualMatchedMoments
open ThermodynamicChart ActualCoframeWeight ActualCoframeLowTime RelativeCoframeJets
open LowSpatialMaterialDerivative TransportMaterialDerivative
set_option maxHeartbeats 1600000

theorem ring_inverse_path_derivative {R : ℝ} {s : Set ℝ} {q : ℝ→Distribution R}
    {q' : Distribution R} {t : ℝ} (hq : HasDerivWithinAt q q' s t)
    (hunit : ∀ z,q t z≠0) :
    HasDerivWithinAt (fun τ => Ring.inverse (q τ))
      (-(Ring.inverse (q t)*q'*Ring.inverse (q t))) s t := by
  have hu : IsUnit (q t) := (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr hunit
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [IsUnit.unit_spec] at h
  have hi : (↑(hu.unit⁻¹) : Distribution R)=Ring.inverse (q t) := by
    rw [←Ring.inverse_unit,IsUnit.unit_spec]
  have hd := h.comp_hasDerivWithinAt t hq
  simpa only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.mulLeftRight_apply,hi] using hd

section Actual
variable (R T : ℝ) (hR : 0<R) (p : ℝ→Space R)
  (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)

def qMoving (t : ℝ) : Distribution R := transport R (-t) (readback (actualQ R T hR p himage t))
def NMoving (t : ℝ) : Distribution R := Ring.inverse (qMoving R T hR p himage t)
def qFirstMoving (a : RealPosition) (t : ℝ) : Distribution R :=
  transport R (-t) (spatialDerivative R 1 (by omega) ![a] (actualQ R T hR p himage t))
def qSecondMoving (a b : RealPosition) (t : ℝ) : Distribution R :=
  transport R (-t) (spatialDerivative R 2 (by omega) ![a,b] (actualQ R T hR p himage t))
def sFirstMoving (a : RealPosition) (t : ℝ) : Distribution R :=
  NMoving R T hR p himage t*qFirstMoving R T hR p himage a t
def sSecondMoving (a b : RealPosition) (t : ℝ) : Distribution R :=
  NMoving R T hR p himage t*qSecondMoving R T hR p himage a b t

theorem qMoving_nonzero {t : ℝ} (ht : t∈Icc 0 T) (z : Phase R) :
    qMoving R T hR p himage t z≠0 :=
  ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht (characteristic (-t) z))

theorem NMoving_actual {t : ℝ} (ht : t∈Icc 0 T) :
    NMoving R T hR p himage t=transport R (-t)
      (Nfield (actualQ R T hR p himage t)
        (fun z => ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht z))) := by
  ext z
  rw [NMoving,JetReciprocal.continuousMap_ring_inverse _ (qMoving_nonzero R T hR p himage ht)]
  simp only [transport_apply,Nfield,JetReciprocal.inverseJet_readback]
  rfl

def actualBMoving (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) (t : ℝ) : Distribution R := by
  classical
  exact if ht : t∈Icc 0 T then transport R (-t)
    (Bfield (actualQ R T hR p himage t)
      (fun z => ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht z)) n hn v) else 0

def BSecondMoving (a b : RealPosition) (t : ℝ) : Distribution R :=
  (2:ℝ) • (sFirstMoving R T hR p himage a t*sFirstMoving R T hR p himage b t)
def BThirdMoving (a b d : RealPosition) (t : ℝ) : Distribution R :=
  (2:ℝ) • (sFirstMoving R T hR p himage a t*sSecondMoving R T hR p himage b d t+
    sFirstMoving R T hR p himage b t*sSecondMoving R T hR p himage a d t+
    sFirstMoving R T hR p himage d t*sSecondMoving R T hR p himage a b t)-
    (6:ℝ) • (sFirstMoving R T hR p himage a t*sFirstMoving R T hR p himage b t*
      sFirstMoving R T hR p himage d t)

theorem sFirstMoving_actual (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    sFirstMoving R T hR p himage a t=transport R (-t)
      (scaledDerivative (actualQ R T hR p himage t)
        (fun z => ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht z)) 1 (by omega) ![a]) := by
  rw [sFirstMoving,NMoving_actual R T hR p himage ht,scaledDerivative,PhaseEnergy.transport_mul]
  rfl

theorem sSecondMoving_actual (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    sSecondMoving R T hR p himage a b t=transport R (-t)
      (scaledDerivative (actualQ R T hR p himage t)
        (fun z => ne_of_gt (coframeJet_positive R hR (Icc 0 T) p himage ht z)) 2 (by omega) ![a,b]) := by
  rw [sSecondMoving,NMoving_actual R T hR p himage ht,scaledDerivative,PhaseEnergy.transport_mul]
  rfl

theorem actualBMoving_second (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    actualBMoving R T hR p himage 2 (by omega) ![a,b] t=BSecondMoving R T hR p himage a b t := by
  rw [actualBMoving,dif_pos ht,Bfield_second,transport_smul,PhaseEnergy.transport_mul]
  rw [←sFirstMoving_actual R T hR p himage a ht,←sFirstMoving_actual R T hR p himage b ht]
  rfl

theorem actualBMoving_third (a b d : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    actualBMoving R T hR p himage 3 le_rfl ![a,b,d] t=BThirdMoving R T hR p himage a b d t := by
  rw [actualBMoving,dif_pos ht,Bfield_third]
  have hs (u v : Distribution R) : transport R (-t) (u-v)=transport R (-t) u-transport R (-t) v :=
    (transportCLM R (-t)).map_sub u v
  simp only [hs,transport_smul,transport_add,PhaseEnergy.transport_mul,
    ←sFirstMoving_actual R T hR p himage _ ht,←sSecondMoving_actual R T hR p himage _ _ ht]
  rfl

variable (c : ℝ)
def qMovingRate (t : ℝ) : Distribution R := transport R (-t)
  (coframeTimeRate R hR (Icc 0 T) c p himage t+advection R (actualQ R T hR p himage t))
def NMovingRate (t : ℝ) : Distribution R :=
  -(NMoving R T hR p himage t*qMovingRate R T hR p himage c t*NMoving R T hR p himage t)
def qFirstMovingRate (a : RealPosition) (t : ℝ) : Distribution R := transport R (-t)
  (firstRate R T hR p himage a t+fieldAdvection R (firstDerivativeField R (actualQ R T hR p himage t) a))
def qSecondMovingRate (a b : RealPosition) (t : ℝ) : Distribution R := transport R (-t)
  (secondRate R T hR p himage a b t+fieldAdvection R (secondDerivativeField R (actualQ R T hR p himage t) a b))
def sFirstMovingRate (a : RealPosition) (t : ℝ) : Distribution R :=
  NMovingRate R T hR p himage c t*qFirstMoving R T hR p himage a t+
    NMoving R T hR p himage t*qFirstMovingRate R T hR p himage a t
def sSecondMovingRate (a b : RealPosition) (t : ℝ) : Distribution R :=
  NMovingRate R T hR p himage c t*qSecondMoving R T hR p himage a b t+
    NMoving R T hR p himage t*qSecondMovingRate R T hR p himage a b t

def BSecondMovingRate (a b : RealPosition) (t : ℝ) : Distribution R :=
  (2:ℝ) • (sFirstMovingRate R T hR p himage c a t*sFirstMoving R T hR p himage b t+
    sFirstMoving R T hR p himage a t*sFirstMovingRate R T hR p himage c b t)
def BThirdMovingRate (a b d : RealPosition) (t : ℝ) : Distribution R :=
  (2:ℝ) • ((sFirstMovingRate R T hR p himage c a t*sSecondMoving R T hR p himage b d t+
    sFirstMoving R T hR p himage a t*sSecondMovingRate R T hR p himage c b d t)+
    (sFirstMovingRate R T hR p himage c b t*sSecondMoving R T hR p himage a d t+
    sFirstMoving R T hR p himage b t*sSecondMovingRate R T hR p himage c a d t)+
    (sFirstMovingRate R T hR p himage c d t*sSecondMoving R T hR p himage a b t+
    sFirstMoving R T hR p himage d t*sSecondMovingRate R T hR p himage c a b t))-
    (6:ℝ) • ((sFirstMovingRate R T hR p himage c a t*sFirstMoving R T hR p himage b t+
      sFirstMoving R T hR p himage a t*sFirstMovingRate R T hR p himage c b t)*
      sFirstMoving R T hR p himage d t+
      (sFirstMoving R T hR p himage a t*sFirstMoving R T hR p himage b t)*
        sFirstMovingRate R T hR p himage c d t)

variable (hT : 0≤T) (p₀ : Space R) (hp : ContinuousOn p (Icc 0 T))
  (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
    ∫ s in (0:ℝ)..t,c • transport R (t-s)
      (SpatialCollision.collision R hR.le (readback (p s))))
include hp he hT

theorem NMoving_hasDerivWithinAt {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (NMoving R T hR p himage) (NMovingRate R T hR p himage c t) (Icc 0 T) t :=
  ring_inverse_path_derivative (actualQ_material R T hR p himage hT c p₀ hp he ht)
    (qMoving_nonzero R T hR p himage ht)

theorem sFirstMoving_hasDerivWithinAt (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (sFirstMoving R T hR p himage a)
      (sFirstMovingRate R T hR p himage c a t) (Icc 0 T) t :=
  (NMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he ht).mul
    (actualQ_first_material R T hR p himage hT c p₀ hp he a ht)

theorem sSecondMoving_hasDerivWithinAt (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (sSecondMoving R T hR p himage a b)
      (sSecondMovingRate R T hR p himage c a b t) (Icc 0 T) t :=
  (NMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he ht).mul
    (actualQ_second_material R T hR p himage hT c p₀ hp he a b ht)

omit hp he hT in
theorem actualBMoving_zero_derivative (v : Fin 0→RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (actualBMoving R T hR p himage 0 (by omega) v) 0 (Icc 0 T) t := by
  apply (hasDerivWithinAt_const t (Icc 0 T) (ContinuousMap.const (Phase R) (2:ℝ))).congr_of_mem _ ht
  intro τ hτ
  rw [actualBMoving,dif_pos hτ,Bfield_zero]
  rfl

omit hp he hT in
theorem actualBMoving_first_derivative (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (actualBMoving R T hR p himage 1 (by omega) ![a]) 0 (Icc 0 T) t := by
  apply (hasDerivWithinAt_const t (Icc 0 T) (0:Distribution R)).congr_of_mem _ ht
  intro τ hτ
  rw [actualBMoving,dif_pos hτ,Bfield_first]
  rfl

theorem actualBMoving_second_derivative (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (actualBMoving R T hR p himage 2 (by omega) ![a,b])
      (BSecondMovingRate R T hR p himage c a b t) (Icc 0 T) t := by
  have h := ((sFirstMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he a ht).mul
    (sFirstMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he b ht)).const_smul (2:ℝ)
  exact h.congr_of_mem (fun τ hτ => actualBMoving_second R T hR p himage a b hτ) ht

theorem actualBMoving_third_derivative (a b d : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (actualBMoving R T hR p himage 3 le_rfl ![a,b,d])
      (BThirdMovingRate R T hR p himage c a b d t) (Icc 0 T) t := by
  have h1 := sFirstMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he
  have h2 := sSecondMoving_hasDerivWithinAt R T hR p himage c hT p₀ hp he
  have h := ((((h1 a ht).mul (h2 b d ht)).add ((h1 b ht).mul (h2 a d ht))).add
    ((h1 d ht).mul (h2 a b ht))).const_smul (2:ℝ) |>.sub
    ((((h1 a ht).mul (h1 b ht)).mul (h1 d ht)).const_smul (6:ℝ))
  exact h.congr_of_mem (fun τ hτ => actualBMoving_third R T hR p himage a b d hτ) ht
end Actual

end
end Resonance.ActualCoframeBMaterial

#check Resonance.ActualCoframeBMaterial.ring_inverse_path_derivative
#check Resonance.ActualCoframeBMaterial.qMoving_nonzero
#check Resonance.ActualCoframeBMaterial.NMoving_actual
#check Resonance.ActualCoframeBMaterial.sFirstMoving_actual
#check Resonance.ActualCoframeBMaterial.sSecondMoving_actual
#check Resonance.ActualCoframeBMaterial.actualBMoving_second
#check Resonance.ActualCoframeBMaterial.actualBMoving_third
#check Resonance.ActualCoframeBMaterial.NMoving_hasDerivWithinAt
#check Resonance.ActualCoframeBMaterial.sFirstMoving_hasDerivWithinAt
#check Resonance.ActualCoframeBMaterial.sSecondMoving_hasDerivWithinAt
#check Resonance.ActualCoframeBMaterial.actualBMoving_zero_derivative
#check Resonance.ActualCoframeBMaterial.actualBMoving_first_derivative
#check Resonance.ActualCoframeBMaterial.actualBMoving_second_derivative
#check Resonance.ActualCoframeBMaterial.actualBMoving_third_derivative
#print axioms Resonance.ActualCoframeBMaterial.ring_inverse_path_derivative
#print axioms Resonance.ActualCoframeBMaterial.qMoving_nonzero
#print axioms Resonance.ActualCoframeBMaterial.NMoving_actual
#print axioms Resonance.ActualCoframeBMaterial.sFirstMoving_actual
#print axioms Resonance.ActualCoframeBMaterial.sSecondMoving_actual
#print axioms Resonance.ActualCoframeBMaterial.actualBMoving_second
#print axioms Resonance.ActualCoframeBMaterial.actualBMoving_third
#print axioms Resonance.ActualCoframeBMaterial.NMoving_hasDerivWithinAt
#print axioms Resonance.ActualCoframeBMaterial.sFirstMoving_hasDerivWithinAt
#print axioms Resonance.ActualCoframeBMaterial.sSecondMoving_hasDerivWithinAt
#print axioms Resonance.ActualCoframeBMaterial.actualBMoving_zero_derivative
#print axioms Resonance.ActualCoframeBMaterial.actualBMoving_first_derivative
#print axioms Resonance.ActualCoframeBMaterial.actualBMoving_second_derivative
#print axioms Resonance.ActualCoframeBMaterial.actualBMoving_third_derivative
