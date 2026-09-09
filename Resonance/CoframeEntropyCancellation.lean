import Resonance.ContinuousMomentPairing
import Resonance.PhaseLogEntropy

/-! The exact cancellations needed by the moving matched entropy.
All three terms are evaluated on the same original phase space and the
coframe is built from the actual five moments, not an independent Euler field. -/
open Set MeasureTheory
namespace Resonance.CoframeEntropyCancellation
noncomputable section
open FreeTransport PhaseEnergy ContinuousCollisionMoments ActualMatchedMoments
open ActualCoframeWeight MatchedContinuousTime Thermodynamics ThermodynamicChart
open JetCollision TransportMaterialDerivative PhaseLogEntropy

theorem collision_parameter_pairing_zero {R : ℝ} (hR : 0 ≤ R)
    (f : Distribution R) (a : C(SpatialTorus,Parameter)) :
    integralCLM R (SpatialCollision.collision R hR f*denominatorField R a)=0 := by
  change (∫ z,(SpatialCollision.collision R hR f*denominatorField R a) z ∂phaseMeasure R)=0
  rw [phaseMeasure,integral_prod _ (continuous_integrable R _)]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro X
  have h := collision_five_moments hR (f.curry X) (a X)
  rw [moment_integral] at h
  convert h using 1
  apply integral_congr_ae
  apply ae_of_all
  intro k
  change FiberContinuity.collisionMap R hR (f.curry X) k*
    WeightedPhysicalForm.reciprocalProfile (a X) k=
    WeightedPhysicalForm.reciprocalProfile (a X) k*FiberContinuity.collisionMap R hR (f.curry X) k
  ring

theorem coframeJet_matchedField (R : ℝ) (hR : 0 < R) (s : Set ℝ) (p : ℝ→Space R)
    (hi : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) :
    readback (coframeJet R hR s p hi t)=
      denominatorField R (matchedField R hR (readback (p t)) (hi t ht)) := by
  rw [coframeJet_readback]
  congr 1
  ext X : 1
  exact parameterPath_apply R hR s _ hi ht X

theorem coframe_time_pairing_zero (R : ℝ) (hR : 0 < R) (s : Set ℝ) (c : ℝ) (p : ℝ→Space R)
    (hi : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) :
    integralCLM R ((readback (p t)-Ring.inverse (readback (coframeJet R hR s p hi t)))*
      coframeTimeRate R hR s c p hi t)=0 := by
  rw [mul_comm,coframeJet_matchedField R hR s p hi ht]
  exact ContinuousMomentPairing.matched_parameter_pairing_zero R hR _ (hi t ht) _

theorem coframe_collision_pairing_zero (R : ℝ) (hR : 0 < R) (s : Set ℝ) (p : ℝ→Space R)
    (hi : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R) (t : ℝ) :
    integralCLM R (SpatialCollision.collision R hR.le (readback (p t))*
      readback (coframeJet R hR s p hi t))=0 := by
  rw [coframeJet_readback]
  exact collision_parameter_pairing_zero hR.le _ _

theorem coframe_equilibrium_transport_zero (R : ℝ) (hR : 0 < R) (s : Set ℝ) (p : ℝ→Space R)
    (hi : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) :
    integralCLM R (Ring.inverse (readback (coframeJet R hR s p hi t))*
      advection R (coframeJet R hR s p hi t))=0 := by
  rw [mul_comm]
  exact entropy_advection_zero R _ (fun z=>(coframeJet_positive R hR s p hi ht z).ne')

end
end Resonance.CoframeEntropyCancellation
