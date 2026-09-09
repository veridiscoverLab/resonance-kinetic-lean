import Resonance.ActualCoframeWeight
import Resonance.ReciprocalThirdJets
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The reciprocal is constructed in the actual compatible spatial jet space.
No differentiability in momentum and no independent jet fields are assumed. -/
open Set Function
open scoped ContDiff
namespace Resonance.JetReciprocal
noncomputable section
open FreeTransport SpatialChainRule JetCollision
set_option maxHeartbeats 1500000

def inverseDistribution {R : ℝ} (f : Distribution R) (hf : ∀ z,f z≠0) : Distribution R :=
  ⟨fun z => (f z)⁻¹,f.continuous.inv₀ hf⟩

theorem continuousMap_ring_inverse {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f : C(K,ℝ)) (hf : ∀ k,f k≠0) (k : K) : Ring.inverse f k=(f k)⁻¹ := by
  have hu : IsUnit f := (ContinuousMap.isUnit_iff_forall_ne_zero f).mpr hf
  have h := congrArg (fun g : C(K,ℝ) => g k) (Ring.inverse_mul_cancel f hu)
  change Ring.inverse f k*f k=1 at h
  simpa only [one_div] using (eq_div_iff (hf k)).mpr h

theorem inverse_realLift {R : ℝ} (f : Distribution R) (hf : ∀ z,f z≠0) :
    realLift (inverseDistribution f hf)=Ring.inverse ∘ realLift f := by
  funext x
  ext k
  exact (continuousMap_ring_inverse (realLift f x) (fun k => hf (torusQuotient x,k)) k).symm

theorem inverse_contDiff {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0) :
    ContDiff ℝ 3 (realLift (inverseDistribution (readback q) hq)) := by
  rw [inverse_realLift]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hu : IsUnit (realLift (readback q) x) :=
    (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr (fun k => hq (torusQuotient x,k))
  have hi := contDiffAt_ringInverse (n := 3) ℝ hu.unit
  rw [IsUnit.unit_spec] at hi
  exact hi.comp x (SpatialJetSpace.toDistribution_contDiff q).contDiffAt

def inverseJet {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0) : Space R :=
  SpatialJetDescent.jetOfDistribution (inverseDistribution (readback q) hq)
    (inverse_contDiff q hq)

@[simp] theorem inverseJet_readback {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0)
    (z : Phase R) : readback (inverseJet q hq) z=(readback q z)⁻¹ := by
  have h := SpatialJetDescent.jetOfDistribution_readback
    (inverseDistribution (readback q) hq) (inverse_contDiff q hq)
  exact congrArg (fun f : Distribution R => f z) h

def scalarOrbit {R : ℝ} (q : Space R) (z : Phase R) (x : RealPosition) : ℝ :=
  SpatialTranslationOrbit.distributionOrbit (readback q) x z

theorem scalarOrbit_contDiff {R : ℝ} (q : Space R) (z : Phase R) :
    ContDiff ℝ 3 (scalarOrbit q z) := by
  let L : Distribution R →L[ℝ] ℝ := ContinuousMap.evalCLM (R := ℝ) z
  exact L.contDiff.comp (SpatialTranslationOrbit.distributionOrbit_contDiff q)

theorem scalarOrbit_zero {R : ℝ} (q : Space R) (z : Phase R) :
    scalarOrbit q z 0=readback q z := by
  change readback q (torusQuotient 0+z.1,z.2)=readback q z
  have h : torusQuotient (0 : RealPosition)=(0 : SpatialTorus) := by
    ext i
    simp [torusQuotient]
  rw [h,zero_add]

theorem spatialDerivative_scalar {R : ℝ} (q : Space R) (z : Phase R)
    (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
    JetEnergy.spatialDerivative R n hn v q z=iteratedFDeriv ℝ n (scalarOrbit q z) 0 v := by
  have h := (ContinuousMap.evalCLM (R := ℝ) z).iteratedFDeriv_comp_left (x := (0 : RealPosition))
    (SpatialTranslationOrbit.distributionOrbit_contDiff q).contDiffAt (by exact_mod_cast hn)
  exact (congrArg (fun A => A v) h).symm

theorem inverse_scalarOrbit {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0)
    (z : Phase R) : scalarOrbit (inverseJet q hq) z=fun x => (scalarOrbit q z x)⁻¹ := by
  funext x
  exact inverseJet_readback q hq (torusQuotient x+z.1,z.2)

theorem inverse_spatialDerivative {R : ℝ} (q : Space R) (hq : ∀ z,readback q z≠0)
    (z : Phase R) (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
    JetEnergy.spatialDerivative R n hn v (inverseJet q hq) z=
      ReciprocalThirdJets.reciprocalJet n (scalarOrbit q z) 0 v := by
  rw [spatialDerivative_scalar,inverse_scalarOrbit]
  rfl

def matchedProfileJet (R : ℝ) (hR : 0<R) (s : Set ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,ActualMatchedMoments.actualMoments R (readback (p t)) X∈
      ThermodynamicChart.momentImage R) (t : ℝ) (ht : t∈s) : Space R :=
  inverseJet (ActualCoframeWeight.coframeJet R hR s p himage t)
    (fun z => ne_of_gt (ActualCoframeWeight.coframeJet_positive R hR s p himage ht z))

theorem matchedProfileJet_actual (R : ℝ) (hR : 0<R) (s : Set ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,ActualMatchedMoments.actualMoments R (readback (p t)) X∈
      ThermodynamicChart.momentImage R) (t : ℝ) (ht : t∈s) (z : Phase R) :
    readback (matchedProfileJet R hR s p himage t ht) z=
      WeightedJointMeasure.profile (ActualMatchedMoments.matchedValue R hR (readback (p t)) z.1) z.2 := by
  rw [matchedProfileJet,inverseJet_readback,ActualCoframeWeight.coframeJet_actual_value R hR s p himage ht,
    inv_inv]

end
end Resonance.JetReciprocal

#check Resonance.JetReciprocal.continuousMap_ring_inverse
#check Resonance.JetReciprocal.inverse_realLift
#check Resonance.JetReciprocal.inverse_contDiff
#check Resonance.JetReciprocal.inverseJet_readback
#check Resonance.JetReciprocal.scalarOrbit_contDiff
#check Resonance.JetReciprocal.scalarOrbit_zero
#check Resonance.JetReciprocal.spatialDerivative_scalar
#check Resonance.JetReciprocal.inverse_scalarOrbit
#check Resonance.JetReciprocal.inverse_spatialDerivative
#check Resonance.JetReciprocal.matchedProfileJet_actual
#print axioms Resonance.JetReciprocal.continuousMap_ring_inverse
#print axioms Resonance.JetReciprocal.inverse_realLift
#print axioms Resonance.JetReciprocal.inverse_contDiff
#print axioms Resonance.JetReciprocal.inverseJet_readback
#print axioms Resonance.JetReciprocal.scalarOrbit_contDiff
#print axioms Resonance.JetReciprocal.scalarOrbit_zero
#print axioms Resonance.JetReciprocal.spatialDerivative_scalar
#print axioms Resonance.JetReciprocal.inverse_scalarOrbit
#print axioms Resonance.JetReciprocal.inverse_spatialDerivative
#print axioms Resonance.JetReciprocal.matchedProfileJet_actual
