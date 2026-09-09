import Resonance.CrossPairDensity
import Resonance.FrequencyGramDecomposition

/-! Changing the actual joint-pair density to the product of its actual
one-leg marginals.  Every division is justified on the same measure;
this is the normalization used in the Hilbert--Schmidt estimate. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.NormalizedPairDensity
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]

def productWeight (a : X→ℝ≥0∞) (b : Y→ℝ≥0∞) (p : X×Y) : ℝ≥0∞ := a p.1*b p.2
def normalized (a : X→ℝ≥0∞) (b : Y→ℝ≥0∞) (r : X×Y→ℝ≥0∞) (p : X×Y) : ℝ≥0∞ :=
  r p/productWeight a b p

theorem productWeight_measurable {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) : Measurable (productWeight a b) :=
  (ha.comp measurable_fst).mul (hb.comp measurable_snd)

theorem normalized_measurable {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞} {r : X×Y→ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hr : Measurable r) :
    Measurable (normalized a b r) := hr.div (productWeight_measurable ha hb)

omit [SFinite μ] [SFinite ν] in
theorem productWeight_valid_ae {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞}
    (ha : ∀ᵐ x∂μ,a x≠0∧a x≠∞) (hb : ∀ᵐ y∂ν,b y≠0∧b y≠∞) :
    ∀ᵐ p∂μ.prod ν,productWeight a b p≠0∧productWeight a b p≠∞ := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=ν)).ae ha,
    (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=ν)).ae hb] with p hpa hpb
  exact ⟨mul_ne_zero hpa.1 hpb.1,ENNReal.mul_ne_top hpa.2 hpb.2⟩

omit [SFinite μ] in
theorem normalized_pair_measure {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞} {r : X×Y→ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hr : Measurable r)
    (hva : ∀ᵐ x∂μ,a x≠0∧a x≠∞) (hvb : ∀ᵐ y∂ν,b y≠0∧b y≠∞) :
    ((μ.withDensity a).prod (ν.withDensity b)).withDensity (normalized a b r)=
      (μ.prod ν).withDensity r := by
  rw [prod_withDensity ha hb]
  change ((μ.prod ν).withDensity (productWeight a b)).withDensity (normalized a b r)=_
  rw [←withDensity_mul _ (productWeight_measurable ha hb)
    (normalized_measurable ha hb hr)]
  apply withDensity_congr_ae
  filter_upwards [productWeight_valid_ae μ ν hva hvb] with p hp
  change productWeight a b p*(r p/productWeight a b p)=r p
  rw [mul_comm,ENNReal.div_mul_cancel hp.1 hp.2]

theorem square_normalization_identity {w r : ℝ≥0∞} (hw0 : w≠0) (hwt : w≠∞) :
    w*(r/w)^2=r^2/w := by
  rw [div_eq_mul_inv,div_eq_mul_inv]
  calc
    _ = (w*w⁻¹)*(r^2*w⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hw0 hwt,one_mul]

omit [SFinite μ] in
theorem normalized_square_lintegral {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞} {r : X×Y→ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hr : Measurable r)
    (hva : ∀ᵐ x∂μ,a x≠0∧a x≠∞) (hvb : ∀ᵐ y∂ν,b y≠0∧b y≠∞) :
    (∫⁻ p,(normalized a b r p)^2∂(μ.withDensity a).prod (ν.withDensity b))=
      ∫⁻ p,(r p)^2/productWeight a b p∂μ.prod ν := by
  rw [prod_withDensity ha hb]
  change (∫⁻ p,(normalized a b r p)^2∂(μ.prod ν).withDensity (productWeight a b))=_
  have hwd := lintegral_withDensity_eq_lintegral_mul (μ.prod ν)
    (productWeight_measurable ha hb) ((normalized_measurable ha hb hr).pow_const 2)
  rw [hwd]
  apply lintegral_congr_ae
  filter_upwards [productWeight_valid_ae μ ν hva hvb] with p hp
  exact square_normalization_identity hp.1 hp.2

def realKernel (a : X→ℝ≥0∞) (b : Y→ℝ≥0∞) (r : X×Y→ℝ≥0∞) (p : X×Y) : ℝ :=
  (normalized a b r p).toReal

theorem realKernel_measurable {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞} {r : X×Y→ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hr : Measurable r) :
    Measurable (realKernel a b r) := (normalized_measurable ha hb hr).ennreal_toReal

omit [SFinite μ] in
theorem normalized_real_measure {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞} {r : X×Y→ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hr : Measurable r)
    (hva : ∀ᵐ x∂μ,a x≠0∧a x≠∞) (hvb : ∀ᵐ y∂ν,b y≠0∧b y≠∞)
    (hrf : ∀ᵐ p∂μ.prod ν,r p≠∞) :
    ((μ.withDensity a).prod (ν.withDensity b)).withDensity
      (fun p=>ENNReal.ofReal (realKernel a b r p))=(μ.prod ν).withDensity r := by
  have hac : (μ.withDensity a).prod (ν.withDensity b) ≪ μ.prod ν := by
    rw [prod_withDensity ha hb]
    exact withDensity_absolutelyContinuous _ _
  calc
    _ = ((μ.withDensity a).prod (ν.withDensity b)).withDensity (normalized a b r) := by
      apply withDensity_congr_ae
      filter_upwards [hac.ae_le (productWeight_valid_ae μ ν hva hvb),hac.ae_le hrf]
        with p hp hpr
      exact ENNReal.ofReal_toReal (ENNReal.div_ne_top hpr hp.1)
    _ = _ := normalized_pair_measure μ ν ha hb hr hva hvb

omit [SFinite μ] in
theorem realKernel_memLp_of_energy {a : X→ℝ≥0∞} {b : Y→ℝ≥0∞} {r : X×Y→ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hr : Measurable r)
    (hva : ∀ᵐ x∂μ,a x≠0∧a x≠∞) (hvb : ∀ᵐ y∂ν,b y≠0∧b y≠∞)
    (he : (∫⁻ p,(r p)^2/productWeight a b p∂μ.prod ν)<∞) :
    MemLp (realKernel a b r) 2 ((μ.withDensity a).prod (ν.withDensity b)) := by
  have hm := realKernel_measurable ha hb hr
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  refine ⟨(hm.pow_const 2).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p=>sq_nonneg (realKernel a b r p)))]
  apply lt_of_le_of_lt (lintegral_mono (fun p=>?_))
    ((normalized_square_lintegral μ ν ha hb hr hva hvb).symm ▸ he)
  change ENNReal.ofReal ((normalized a b r p).toReal^2)≤(normalized a b r p)^2
  rw [pow_two,pow_two,ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact mul_le_mul' ENNReal.ofReal_toReal_le ENNReal.ofReal_toReal_le

end
end Resonance.NormalizedPairDensity
