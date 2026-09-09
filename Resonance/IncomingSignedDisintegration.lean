import Resonance.CubeContinuousEssentialNorm

/-! Signed integrals in the original incoming-sphere parametrization.
Actual integrability is transported along the full measure identity
before any signed change of variables or subsequent Fubini argument. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.IncomingSignedDisintegration
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure IncomingPairMarginal

def coefficient (R : ℝ) (p : (E×E)×Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (‖p.1.1-p.1.2‖/8)*
    (CoareaNormalization.allFourFlags R).indicator (fun _=>1) (incomingQuartet p)

theorem coefficient_measurable (R : ℝ) : Measurable (coefficient R) :=
  (show Measurable (fun p : (E×E)×Sphere=>ENNReal.ofReal (‖p.1.1-p.1.2‖/8)) by fun_prop).mul
    ((measurable_const.indicator (CoareaNormalization.allFourFlags_measurable R)).comp
      incomingQuartet_measurable)

theorem coefficient_finite (R : ℝ) (p : (E×E)×Sphere) : coefficient R p<∞ := by
  unfold coefficient
  by_cases h : incomingQuartet p∈CoareaNormalization.allFourFlags R
  · simp only [Set.indicator_of_mem h,mul_one]
    exact ENNReal.ofReal_lt_top
  · simp only [Set.indicator_of_notMem h,mul_zero,ENNReal.zero_lt_top]

def incomingMeasure (R : ℝ) : Measure ((E×E)×Sphere) :=
  pairSphereVolume.withDensity (coefficient R)

theorem incomingMeasure_map (R : ℝ) :
    Measure.map incomingQuartet (incomingMeasure R)=pairingMeasure R := by
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  rw [lintegral_map hΦ incomingQuartet_measurable,incomingMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul pairSphereVolume
    (f:=coefficient R) (g:=fun p=>Φ (incomingQuartet p)) (coefficient_measurable R)
      (hΦ.comp incomingQuartet_measurable),pairing_incoming_lintegral R Φ hΦ]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply]
  unfold coefficient
  by_cases h : incomingQuartet p∈CoareaNormalization.allFourFlags R
  · simp only [Set.indicator_of_mem h,mul_one]
  · simp only [Set.indicator_of_notMem h,mul_zero,zero_mul]

theorem incoming_integrable (R : ℝ) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    Integrable (fun p=>Φ (incomingQuartet p)) (incomingMeasure R) := by
  apply (integrable_map_measure hΦ.aestronglyMeasurable incomingQuartet_measurable.aemeasurable).mp
  rwa [incomingMeasure_map R]

theorem density_integrable (R : ℝ) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    Integrable (fun p=>(coefficient R p).toReal*Φ (incomingQuartet p)) pairSphereVolume := by
  exact (integrable_withDensity_iff_integrable_smul' (coefficient_measurable R)
    (ae_of_all _ (coefficient_finite R))).mp (incoming_integrable R Φ hΦ hi)

theorem density_integral (R : ℝ) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (_hi : Integrable Φ (pairingMeasure R)) :
    (∫q,Φ q∂pairingMeasure R)=∫p,(coefficient R p).toReal*Φ (incomingQuartet p)∂pairSphereVolume := by
  rw [←incomingMeasure_map R,integral_map incomingQuartet_measurable.aemeasurable
    hΦ.aestronglyMeasurable,incomingMeasure]
  exact integral_withDensity_eq_integral_toReal_smul (coefficient_measurable R)
    (ae_of_all _ (coefficient_finite R)) _

theorem coefficient_signed (R : ℝ) (Φ : FourMomenta→ℝ) (p : (E×E)×Sphere) :
    (coefficient R p).toReal*Φ (incomingQuartet p)=
      (‖p.1.1-p.1.2‖/8)*CoareaNormalization.sharpReadout R Φ (incomingQuartet p) := by
  unfold coefficient CoareaNormalization.sharpReadout
  by_cases h : incomingQuartet p∈CoareaNormalization.allFourFlags R
  · simp only [Set.indicator_of_mem h,mul_one,ENNReal.toReal_ofReal (by positivity : 0≤‖p.1.1-p.1.2‖/8)]
  · simp only [Set.indicator_of_notMem h,mul_zero,ENNReal.toReal_zero,zero_mul]

theorem original_incoming_signed_integrable (R : ℝ) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    Integrable (fun p=>(‖p.1.1-p.1.2‖/8)*
      CoareaNormalization.sharpReadout R Φ (incomingQuartet p)) pairSphereVolume := by
  apply (density_integrable R Φ hΦ hi).congr
  exact ae_of_all _ (coefficient_signed R Φ)

theorem original_incoming_signed_integral (R : ℝ) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    (∫q,Φ q∂pairingMeasure R)=∫p,(‖p.1.1-p.1.2‖/8)*
      CoareaNormalization.sharpReadout R Φ (incomingQuartet p)∂pairSphereVolume := by
  rw [density_integral R Φ hΦ hi]
  apply integral_congr_ae
  exact ae_of_all _ (coefficient_signed R Φ)

end
end Resonance.IncomingSignedDisintegration
