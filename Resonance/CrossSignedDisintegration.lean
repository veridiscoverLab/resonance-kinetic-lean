import Resonance.IncomingSignedDisintegration

/-! The signed plane disintegration of the same original quartet
measure. The diagonal uses the original almost-everywhere convention;
all sharp flags are retained and integrability is transported first. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CrossSignedDisintegration
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure CrossPairCoordinates
open PlaneCoarea (E2)

def coefficient (R : ℝ) (p : (E×E)×E2) : ℝ≥0∞ :=
  (1/2 : ℝ≥0∞)*ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹)*
    (CoareaNormalization.allFourFlags R).indicator (fun _=>1) (crossQuartet p)

theorem coefficient_measurable (R : ℝ) : Measurable (coefficient R) :=
  (show Measurable (fun p : (E×E)×E2=>(1/2 : ℝ≥0∞)*ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹))
    by fun_prop).mul ((measurable_const.indicator (CoareaNormalization.allFourFlags_measurable R)).comp
      crossQuartet_measurable)

theorem coefficient_finite (R : ℝ) (p : (E×E)×E2) : coefficient R p<∞ := by
  unfold coefficient
  by_cases h : crossQuartet p∈CoareaNormalization.allFourFlags R
  · simp only [Set.indicator_of_mem h,mul_one]
    exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
  · simp only [Set.indicator_of_notMem h,mul_zero,ENNReal.zero_lt_top]

def crossMeasure (R : ℝ) : Measure ((E×E)×E2) :=
  pairPlaneVolume.withDensity (coefficient R)

theorem crossMeasure_map {R : ℝ} (hR : 0≤R) :
    Measure.map crossQuartet (crossMeasure R)=pairingMeasure R := by
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  rw [lintegral_map hΦ crossQuartet_measurable,crossMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul pairPlaneVolume
    (f:=coefficient R) (g:=fun p=>Φ (crossQuartet p)) (coefficient_measurable R)
      (hΦ.comp crossQuartet_measurable),pairing_cross_lintegral hR Φ hΦ]
  rw [←lintegral_const_mul' (1/2 : ℝ≥0∞) _ (by norm_num)]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply]
  unfold coefficient
  by_cases h : crossQuartet p∈CoareaNormalization.allFourFlags R
  · simp only [Set.indicator_of_mem h,mul_one,mul_assoc]
  · simp only [Set.indicator_of_notMem h,mul_zero,zero_mul]

theorem cross_integrable {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    Integrable (fun p=>Φ (crossQuartet p)) (crossMeasure R) := by
  apply (integrable_map_measure hΦ.aestronglyMeasurable crossQuartet_measurable.aemeasurable).mp
  rwa [crossMeasure_map hR]

theorem density_integrable {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    Integrable (fun p=>(coefficient R p).toReal*Φ (crossQuartet p)) pairPlaneVolume := by
  exact (integrable_withDensity_iff_integrable_smul' (coefficient_measurable R)
    (ae_of_all _ (coefficient_finite R))).mp (cross_integrable hR Φ hΦ hi)

theorem density_integral {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (_hi : Integrable Φ (pairingMeasure R)) :
    (∫q,Φ q∂pairingMeasure R)=∫p,(coefficient R p).toReal*Φ (crossQuartet p)∂pairPlaneVolume := by
  rw [←crossMeasure_map hR,integral_map crossQuartet_measurable.aemeasurable
    hΦ.aestronglyMeasurable,crossMeasure]
  exact integral_withDensity_eq_integral_toReal_smul (coefficient_measurable R)
    (ae_of_all _ (coefficient_finite R)) _

theorem coefficient_signed (R : ℝ) (Φ : FourMomenta→ℝ) (p : (E×E)×E2) :
    (coefficient R p).toReal*Φ (crossQuartet p)=
      (2*‖p.1.2-p.1.1‖)⁻¹*CoareaNormalization.sharpReadout R Φ (crossQuartet p) := by
  unfold coefficient CoareaNormalization.sharpReadout
  by_cases h : crossQuartet p∈CoareaNormalization.allFourFlags R
  · simp only [Set.indicator_of_mem h,mul_one,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _)),ENNReal.toReal_div,
      ENNReal.toReal_one,ENNReal.toReal_ofNat]
    rw [mul_inv_rev]
    ring
  · simp only [Set.indicator_of_notMem h,mul_zero,ENNReal.toReal_zero,zero_mul]

theorem original_cross_signed_integrable {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ)
    (hΦ : Measurable Φ) (hi : Integrable Φ (pairingMeasure R)) :
    Integrable (fun p=>(2*‖p.1.2-p.1.1‖)⁻¹*
      CoareaNormalization.sharpReadout R Φ (crossQuartet p)) pairPlaneVolume := by
  apply (density_integrable hR Φ hΦ hi).congr
  exact ae_of_all _ (coefficient_signed R Φ)

theorem original_cross_signed_integral {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ)
    (hΦ : Measurable Φ) (hi : Integrable Φ (pairingMeasure R)) :
    (∫q,Φ q∂pairingMeasure R)=∫p,(2*‖p.1.2-p.1.1‖)⁻¹*
      CoareaNormalization.sharpReadout R Φ (crossQuartet p)∂pairPlaneVolume := by
  rw [density_integral hR Φ hΦ hi]
  apply integral_congr_ae
  exact ae_of_all _ (coefficient_signed R Φ)

end
end Resonance.CrossSignedDisintegration
