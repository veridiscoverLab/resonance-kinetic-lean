import Resonance.SpacetimeReciprocalIdentity

/-! The original entropy production on the same continuous family is read
as a single nonnegative spacetime-quartet integral. Its sections are exactly
the original cubeProduction; no integrability is supplied by default-zero
Bochner conventions. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeProductionIntegral
noncomputable section
open ResonantMeasure SpacetimePairing SpacetimeContinuousFields
open SpacetimeReciprocalIdentity Collision NonlinearEntropy FiberContinuity
open ContinuousCollisionEntropy

theorem productionField_measurable {R : ℝ} (hR : 0≤R) (T : ℝ)
    {F : Base→C(cube R,ℝ)} (hF : Measurable F) : Measurable (productionField F) := by
  have h (i:Fin 4):Measurable (fun p:Joint=>field F (leg i p)):=
    (field_measurable hF).comp (SpacetimePairing.leg_quasiMeasurePreserving hR T i).measurable
  exact ((((h 0).mul (h 1)).mul (h 2)).mul (h 3)).const_mul (1/4:ℝ) |>.mul
    (((((h 0).inv.add (h 1).inv).sub (h 2).inv).sub (h 3).inv).pow_const 2)

theorem production_field_slice_ae {R : ℝ} (F : Base→C(cube R,ℝ)) (a : Base) :
    (fun q=>productionField F (a,q))=ᵐ[pairingMeasure R]
      productionDensity (continuousExtension R (F a)) := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  have he (i:Fin 4):field F (a,q i)=continuousExtension R (F a) (q i) := by
    rw [continuousExtension_eq R _ ⟨q i,hq.1 i⟩]
    exact field_on_cube F a ⟨q i,hq.1 i⟩
  simp only [productionField,productionDensity,mobility,delta,he]

theorem production_slice_integrable {R : ℝ} (hR : 0≤R)
    (F : Base→C(cube R,ℝ)) (a : Base) (hf : ∀k,0<F a k) :
    Integrable (fun q=>productionField F (a,q)) (pairingMeasure R) :=
  (cubeProduction_integrable_quartet hR (F a) hf).congr (production_field_slice_ae F a).symm

theorem production_slice_lintegral {R : ℝ} (hR : 0≤R)
    (F : Base→C(cube R,ℝ)) (a : Base) (hf : ∀k,0<F a k) :
    (∫⁻q,ENNReal.ofReal (productionField F (a,q))∂pairingMeasure R)=
      ENNReal.ofReal (cubeProduction R (F a)) := by
  calc
    _ = ∫⁻q, ENNReal.ofReal (productionDensity (continuousExtension R (F a)) q)
        ∂pairingMeasure R :=
      lintegral_congr_ae ((production_field_slice_ae F a).fun_comp ENNReal.ofReal)
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      (cubeProduction_integrable_quartet hR (F a) hf)
      (NonlinearEntropy.productionDensity_nonneg_ae (positive_extension (F a) hf))).symm

theorem full_production_lintegral {R : ℝ} (hR : 0≤R) (T : ℝ)
    {F : Base→C(cube R,ℝ)} (hFm : Measurable F)
    (hf : ∀ᵐa∂baseMeasure T,∀k,0<F a k) :
    (∫⁻p,ENNReal.ofReal (productionField F p)∂SpacetimePairing.jointMeasure R T)=
      ∫⁻a,ENNReal.ofReal (cubeProduction R (F a))∂baseMeasure T := by
  letI:=pairingMeasure_finite hR
  rw [SpacetimePairing.jointMeasure,lintegral_prod _
    (productionField_measurable hR T hFm).ennreal_ofReal.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hf] with a ha
  exact production_slice_lintegral hR F a ha

end
end Resonance.SpacetimeProductionIntegral
