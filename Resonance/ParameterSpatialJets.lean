import Resonance.ActualCoframeWeight

/-! Actual ordered derivatives of the five-parameter field on the same torus.
These fields are obtained by differentiation, not supplied as independent data. -/
open Set Function
open scoped ContDiff
namespace Resonance.ParameterSpatialJets
noncomputable section
open FreeTransport SpatialChainRule SpatialJetSpace SpatialJetDescent SpatialTranslationOrbit
open JetCollision ActualCoframeWeight Thermodynamics
set_option maxHeartbeats 1200000

section General
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def firstField (a : C(SpatialTorus,F)) (ha : ContDiff ℝ 1 (fieldLift a)) :
    C(SpatialTorus,RealPosition→L[ℝ]F) :=
  descend (fderiv ℝ (fieldLift a)) (ha.continuous_fderiv (by norm_num))
    (fderiv_invariant (fieldLift_invariant a))

theorem firstField_lift (a : C(SpatialTorus,F)) (ha : ContDiff ℝ 1 (fieldLift a)) :
    fieldLift (firstField a ha)=fderiv ℝ (fieldLift a) := descend_lift _ _ _

theorem firstField_graph (a : C(SpatialTorus,F)) (ha : ContDiff ℝ 1 (fieldLift a)) :
    (a,firstField a ha)∈fieldDerivativeGraph := by
  intro x
  change HasFDerivAt (fieldLift a) (fieldLift (firstField a ha) x) x
  rw [firstField_lift]
  exact (ha.differentiable (by norm_num) x).hasFDerivAt

theorem full_translation_contDiff (a : C(SpatialTorus,F))
    (ha : ContDiff ℝ 3 (fieldLift a)) : ContDiff ℝ 3 (translateField a) := by
  let a1 := firstField a (ha.of_le (by norm_num))
  have h1 : ContDiff ℝ 2 (fieldLift a1) := by
    rw [firstField_lift]
    exact ha.fderiv_right (by norm_num)
  let a2 := firstField a1 (h1.of_le (by norm_num))
  have h2 : ContDiff ℝ 1 (fieldLift a2) := by
    rw [firstField_lift]
    exact h1.fderiv_right (by norm_num)
  let a3 := firstField a2 h2
  have h3 : ContDiff ℝ 0 (translateField a3) := contDiff_zero.mpr (translateField_continuous a3)
  exact translateField_contDiff_succ (firstField_graph a _) <|
    translateField_contDiff_succ (firstField_graph a1 _) <|
      translateField_contDiff_succ (firstField_graph a2 _) h3

end General

def parameterDerivative (a : C(SpatialTorus,Parameter)) (n : ℕ)
    (v : Fin n→RealPosition) : C(SpatialTorus,Parameter) :=
  iteratedFDeriv ℝ n (translateField a) 0 v

def denominatorJet (R : ℝ) (a : C(SpatialTorus,Parameter))
    (ha : ContDiff ℝ 3 (fieldLift a)) : Space R :=
  jetOfDistribution (denominatorField R a) (by
    rw [denominatorField_realLift]
    exact (denominatorCube R).contDiff.comp ha)

theorem denominatorJet_readback (R : ℝ) (a : C(SpatialTorus,Parameter))
    (ha : ContDiff ℝ 3 (fieldLift a)) :
    readback (denominatorJet R a ha)=denominatorField R a := jetOfDistribution_readback _ _

theorem denominator_orbit (R : ℝ) (a : C(SpatialTorus,Parameter)) :
    distributionOrbit (denominatorField R a)=denominatorField R ∘ translateField a := by
  funext x
  ext z
  rfl

theorem denominator_actual_derivative (R : ℝ) (a : C(SpatialTorus,Parameter))
    (ha : ContDiff ℝ 3 (fieldLift a)) (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
    JetEnergy.spatialDerivative R n hn v (denominatorJet R a ha)=
      denominatorField R (parameterDerivative a n v) := by
  rw [JetEnergy.spatialDerivative_actual,denominatorJet_readback,denominator_orbit]
  have h := (denominatorField R).iteratedFDeriv_comp_left (x := (0 : RealPosition))
    (full_translation_contDiff a ha).contDiffAt (by exact_mod_cast hn)
  exact congrArg (fun A => A v) h

end
end Resonance.ParameterSpatialJets

#check Resonance.ParameterSpatialJets.firstField_lift
#check Resonance.ParameterSpatialJets.firstField_graph
#check Resonance.ParameterSpatialJets.full_translation_contDiff
#check Resonance.ParameterSpatialJets.denominatorJet_readback
#check Resonance.ParameterSpatialJets.denominator_orbit
#check Resonance.ParameterSpatialJets.denominator_actual_derivative
#print axioms Resonance.ParameterSpatialJets.firstField_lift
#print axioms Resonance.ParameterSpatialJets.firstField_graph
#print axioms Resonance.ParameterSpatialJets.full_translation_contDiff
#print axioms Resonance.ParameterSpatialJets.denominatorJet_readback
#print axioms Resonance.ParameterSpatialJets.denominator_orbit
#print axioms Resonance.ParameterSpatialJets.denominator_actual_derivative
