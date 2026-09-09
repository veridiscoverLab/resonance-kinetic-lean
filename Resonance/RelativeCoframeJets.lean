import Resonance.JetReciprocal
import Resonance.ParameterSpatialJets

/-! Exact physical relative coframe, its ordered B-jets, and the complete
collision-moment cancellation. All fields live on the original common phase. -/
open Set MeasureTheory
open scoped ContDiff
namespace Resonance.RelativeCoframeJets
noncomputable section
open FreeTransport JetCollision SpatialChainRule JetEnergy JetReciprocal
open ParameterSpatialJets ActualCoframeWeight ContinuousCollisionMoments PhaseEnergy
set_option maxHeartbeats 1500000

abbrev Nfield {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0) : Distribution R :=
  readback (inverseJet q hq)

def scaledDerivative {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) : Distribution R :=
  Nfield q hq*spatialDerivative R n hn v q

def Bfield {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) : Distribution R :=
  readback q*spatialDerivative R n hn v (inverseJet q hq)+scaledDerivative q hq n hn v

theorem Bfield_scalar {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) (z : Phase R) :
    Bfield q hq n hn v z=ReciprocalThirdJets.coframeB n (scalarOrbit q z) 0 v := by
  simp only [Bfield,scaledDerivative,Nfield,ContinuousMap.add_apply,ContinuousMap.mul_apply,
    inverseJet_readback,spatialDerivative_scalar,inverse_scalarOrbit,
    ReciprocalThirdJets.coframeB,ReciprocalThirdJets.reciprocalJet,ReciprocalThirdJets.scaledJet,scalarOrbit_zero,
    div_eq_mul_inv,inv_inv]
  ring

theorem scaledDerivative_scalar {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) (z : Phase R) :
    scaledDerivative q hq n hn v z=ReciprocalThirdJets.scaledJet n (scalarOrbit q z) 0 v := by
  simp only [scaledDerivative,Nfield,ContinuousMap.mul_apply,inverseJet_readback,
    spatialDerivative_scalar,ReciprocalThirdJets.scaledJet,scalarOrbit_zero]

theorem Bfield_zero {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0) (v : Fin 0→RealPosition) :
    Bfield q hq 0 (by omega) v=ContinuousMap.const _ 2 := by
  ext z
  rw [Bfield_scalar]
  exact ReciprocalThirdJets.coframeB_zero (by simpa only [scalarOrbit_zero] using hq z) v

theorem Bfield_first {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0) (a : RealPosition) :
    Bfield q hq 1 (by omega) ![a]=0 := by
  ext z
  rw [Bfield_scalar]
  exact ReciprocalThirdJets.coframeB_first (by simpa only [scalarOrbit_zero] using hq z)
    ((scalarOrbit_contDiff q z).of_le (by norm_num)).contDiffAt a

theorem Bfield_second {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0) (a b : RealPosition) :
    Bfield q hq 2 (by omega) ![a,b]=
      (2:ℝ) • (scaledDerivative q hq 1 (by omega) ![a]*scaledDerivative q hq 1 (by omega) ![b]) := by
  ext z
  simp only [Bfield_scalar,ContinuousMap.smul_apply,ContinuousMap.mul_apply,smul_eq_mul,
    scaledDerivative_scalar]
  simpa only [mul_assoc] using ReciprocalThirdJets.coframeB_second (x := (0 : RealPosition)) (by simpa only [scalarOrbit_zero] using hq z)
    ((scalarOrbit_contDiff q z).of_le (by norm_num)).contDiffAt a b

theorem Bfield_third {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0) (a b c : RealPosition) :
    Bfield q hq 3 le_rfl ![a,b,c]=
      (2:ℝ) • (scaledDerivative q hq 1 (by omega) ![a]*scaledDerivative q hq 2 (by omega) ![b,c]+
        scaledDerivative q hq 1 (by omega) ![b]*scaledDerivative q hq 2 (by omega) ![a,c]+
        scaledDerivative q hq 1 (by omega) ![c]*scaledDerivative q hq 2 (by omega) ![a,b])-
      (6:ℝ) • (scaledDerivative q hq 1 (by omega) ![a]*scaledDerivative q hq 1 (by omega) ![b]*
        scaledDerivative q hq 1 (by omega) ![c]) := by
  ext z
  simp only [Bfield_scalar,ContinuousMap.smul_apply,ContinuousMap.mul_apply,ContinuousMap.add_apply,
    ContinuousMap.sub_apply,smul_eq_mul,scaledDerivative_scalar]
  simpa only [mul_assoc] using ReciprocalThirdJets.coframeB_third (x := (0 : RealPosition)) (by simpa only [scalarOrbit_zero] using hq z)
    (scalarOrbit_contDiff q z).contDiffAt a b c

def eta {R : ℝ} (f G q : Space R) (hq : ∀ z,readback q z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) : Distribution R :=
  readback q*spatialDerivative R n hn v (f-inverseJet q hq-G)

def relativeH {R : ℝ} (f G q qbar : Space R) (hq : ∀ z,readback q z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) : Distribution R :=
  eta f G q hq n hn v-Nfield q hq*spatialDerivative R n hn v (q-qbar)

/-- The original H-identity: the highest actual parameter derivative has
cancelled, leaving the complete differentiated f-G and the reference jet. -/
theorem H_identity {R : ℝ} (f G q qbar : Space R) (hq : ∀ z,readback q z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
    relativeH f G q qbar hq n hn v=
      readback q*spatialDerivative R n hn v (f-G)+Nfield q hq*spatialDerivative R n hn v qbar-
        Bfield q hq n hn v := by
  simp only [relativeH,eta,Bfield,scaledDerivative,map_sub]
  ring

/-- Each differentiated reciprocal parameter remains the entire five-moment
polynomial, with coefficients differentiated on the same torus. -/
theorem macro_difference_derivative (R : ℝ)
    (a b : C(SpatialTorus,Thermodynamics.Parameter))
    (ha : ContDiff ℝ 3 (SpatialJetSpace.fieldLift a))
    (hb : ContDiff ℝ 3 (SpatialJetSpace.fieldLift b))
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
    spatialDerivative R n hn v (denominatorJet R a ha-denominatorJet R b hb)=
      parameterWeight R (parameterDerivative a n v-parameterDerivative b n v) := by
  rw [map_sub,denominator_actual_derivative,denominator_actual_derivative,←map_sub]
  rfl

/-- The kernel term cancels against the complete collision output of the same
state, after actual spatial differentiation. This uses the proved original
collision moments, not a separately posited projection property. -/
theorem H_collision_pairing {R : ℝ} (hR : 0≤R)
    (f G p : Space R) (a b : C(SpatialTorus,Thermodynamics.Parameter))
    (ha : ContDiff ℝ 3 (SpatialJetSpace.fieldLift a))
    (hb : ContDiff ℝ 3 (SpatialJetSpace.fieldLift b))
    (hq : ∀ z,readback (denominatorJet R a ha) z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
    (∫ z,relativeH f G (denominatorJet R a ha) (denominatorJet R b hb) hq n hn v z*
      (spatialDerivative R n hn v (JetCollision.collision R hR p) z/
        Nfield (denominatorJet R a ha) hq z) ∂phaseMeasure R)=
    ∫ z,eta f G (denominatorJet R a ha) hq n hn v z*
      (spatialDerivative R n hn v (JetCollision.collision R hR p) z/
        Nfield (denominatorJet R a ha) hq z) ∂phaseMeasure R := by
  simp only [relativeH,macro_difference_derivative,ContinuousMap.sub_apply,ContinuousMap.mul_apply]
  exact coframe_collision_test_replacement hR p
    (parameterDerivative a n v-parameterDerivative b n v)
    (Nfield (denominatorJet R a ha) hq) (eta f G (denominatorJet R a ha) hq n hn v)
    (fun z => by simpa only [Nfield,inverseJet_readback,ne_eq,inv_eq_zero] using hq z) n hn v

theorem H_full_collision_difference_pairing {R : ℝ} (hR : 0≤R)
    (f G fapp : Space R) (a b : C(SpatialTorus,Thermodynamics.Parameter))
    (ha : ContDiff ℝ 3 (SpatialJetSpace.fieldLift a))
    (hb : ContDiff ℝ 3 (SpatialJetSpace.fieldLift b))
    (hq : ∀ z,readback (denominatorJet R a ha) z≠0)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
    integralCLM R (relativeH f G (denominatorJet R a ha) (denominatorJet R b hb) hq n hn v*
      (readback (denominatorJet R a ha)*spatialDerivative R n hn v
        (JetCollision.collision R hR f-JetCollision.collision R hR fapp)))=
    integralCLM R (eta f G (denominatorJet R a ha) hq n hn v*
      (readback (denominatorJet R a ha)*spatialDerivative R n hn v
        (JetCollision.collision R hR f-JetCollision.collision R hR fapp))) := by
  have hs (p : Space R) :
      integralCLM R (relativeH f G (denominatorJet R a ha) (denominatorJet R b hb) hq n hn v*
        (readback (denominatorJet R a ha)*spatialDerivative R n hn v (JetCollision.collision R hR p)))=
      integralCLM R (eta f G (denominatorJet R a ha) hq n hn v*
        (readback (denominatorJet R a ha)*spatialDerivative R n hn v (JetCollision.collision R hR p))) := by
    have h := H_collision_pairing hR f G p a b ha hb hq n hn v
    simpa only [Nfield,inverseJet_readback,div_eq_mul_inv,inv_inv,mul_comm] using h
  simp only [map_sub,mul_sub]
  rw [hs f,hs fapp]

end
end Resonance.RelativeCoframeJets

#check Resonance.RelativeCoframeJets.Bfield_scalar
#check Resonance.RelativeCoframeJets.scaledDerivative_scalar
#check Resonance.RelativeCoframeJets.Bfield_zero
#check Resonance.RelativeCoframeJets.Bfield_first
#check Resonance.RelativeCoframeJets.Bfield_second
#check Resonance.RelativeCoframeJets.Bfield_third
#check Resonance.RelativeCoframeJets.H_identity
#check Resonance.RelativeCoframeJets.macro_difference_derivative
#check Resonance.RelativeCoframeJets.H_collision_pairing
#check Resonance.RelativeCoframeJets.H_full_collision_difference_pairing
#print axioms Resonance.RelativeCoframeJets.Bfield_scalar
#print axioms Resonance.RelativeCoframeJets.scaledDerivative_scalar
#print axioms Resonance.RelativeCoframeJets.Bfield_zero
#print axioms Resonance.RelativeCoframeJets.Bfield_first
#print axioms Resonance.RelativeCoframeJets.Bfield_second
#print axioms Resonance.RelativeCoframeJets.Bfield_third
#print axioms Resonance.RelativeCoframeJets.H_identity
#print axioms Resonance.RelativeCoframeJets.macro_difference_derivative
#print axioms Resonance.RelativeCoframeJets.H_collision_pairing
#print axioms Resonance.RelativeCoframeJets.H_full_collision_difference_pairing
