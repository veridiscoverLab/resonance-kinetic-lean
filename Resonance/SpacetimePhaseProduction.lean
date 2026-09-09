import Resonance.SpacetimeProductionIntegral
import Resonance.SpacetimeActualMatching
import Resonance.EntropyWindowCalculus

/-! Exact time and space normalization of the original production. The
space measure is the original torus Haar volume, not a normalized substitute.
Every real integral below has a proved integrability premise. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimePhaseProduction
noncomputable section
open ResonantMeasure FreeTransport PhaseEnergy ContinuousLogPath
open ContinuousCollisionMoments ContinuousCollisionEntropy PhaseCollisionEntropy
open SpacetimePairing SpacetimeContinuousFields SpacetimeProductionIntegral
open SpacetimeActualMatching SpacetimeReciprocalIdentity

theorem production_base_aemeasurable {R : ℝ} (hR : 0 ≤ R) (T : ℝ)
    {F : Base → C(cube R,ℝ)} (hF : Measurable F)
    (hf : ∀ᵐ a ∂baseMeasure T, ∀ k, 0 < F a k) :
    AEMeasurable (fun a => ENNReal.ofReal (cubeProduction R (F a))) (baseMeasure T) := by
  letI := pairingMeasure_finite hR
  have hm := (productionField_measurable hR T hF).ennreal_ofReal.lintegral_prod_right'
    (ν := pairingMeasure R)
  apply hm.aemeasurable.congr
  filter_upwards [hf] with a ha
  exact production_slice_lintegral hR F a ha

theorem production_space_integrable {R : ℝ} (hR : 0 ≤ R)
    (f : Distribution R) (hf : ∀ z, 0 < f z) :
    Integrable (fun X : SpatialTorus => cubeProduction R (f.curry X)) := by
  have hi := (continuous_integrable R
    (SpatialCollision.collision R hR f * Ring.inverse f)).integral_prod_left
  apply hi.congr
  apply ae_of_all
  intro X
  dsimp only
  rw [←actual_collision_entropy hR (f.curry X) (fun k => hf (X,k))]
  change (∫ k, SpatialCollision.collision R hR f (X,k) * Ring.inverse f (X,k)
    ∂momentumMeasure R) =
    ∫ k, FiberContinuity.collisionMap R hR (f.curry X) k *
      Ring.inverse (f.curry X) k ∂momentumMeasure R
  apply integral_congr_ae
  apply ae_of_all
  intro k
  dsimp only
  rw [ring_inverse_apply f (fun z => (hf z).ne'),
    ring_inverse_apply (f.curry X) (fun k => (hf (X,k)).ne')]
  rfl

theorem production_space_lintegral {R : ℝ} (hR : 0 ≤ R)
    (f : Distribution R) (hf : ∀ z, 0 < f z) :
    (∫⁻ X : SpatialTorus, ENNReal.ofReal (cubeProduction R (f.curry X))) =
      ENNReal.ofReal (phaseProduction R f) := by
  exact (ofReal_integral_eq_lintegral_ofReal (production_space_integrable hR f hf)
    (ae_of_all _ (fun X => cubeProduction_nonnegative (f.curry X) (fun k => hf (X,k))))).symm

theorem original_time_space_production {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (f : ℝ → Distribution R) (hF : Measurable (cubeFamily f))
    (hc : ContinuousOn f (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, ∀ z, 0 < f t z) :
    (∫⁻ a, ENNReal.ofReal (cubeProduction R (cubeFamily f a)) ∂baseMeasure T) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..T, phaseProduction R (f t)) := by
  have hf : ∀ᵐ a ∂baseMeasure T, ∀ k, 0 < cubeFamily f a k := by
    apply (quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
    intro a ha k
    exact hp a.1 ha (a.2,k)
  have hd := EntropyWindowCalculus.phaseProduction_continuousOn hR hc hp
  have hi : IntegrableOn (fun t => phaseProduction R (f t)) (Icc 0 T) :=
    hd.integrableOn_Icc
  calc
    _ = ∫⁻ t in Icc 0 T, ∫⁻ X : SpatialTorus,
        ENNReal.ofReal (cubeProduction R ((f t).curry X)) := by
      exact lintegral_prod _ (production_base_aemeasurable hR T hF hf)
    _ = ∫⁻ t in Icc 0 T, ENNReal.ofReal (phaseProduction R (f t)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact production_space_lintegral hR (f t) (hp t ht)
    _ = ENNReal.ofReal (∫ t in Icc 0 T, phaseProduction R (f t)) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        ((ae_restrict_mem measurableSet_Icc).mono
          (fun t ht => phaseProduction_nonnegative (f t) (hp t ht)))).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

end
end Resonance.SpacetimePhaseProduction
