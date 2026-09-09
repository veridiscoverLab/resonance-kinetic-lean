import Resonance.MarkedConvolutionSupport

/-! Continuity of the actual marked sum density at the physical energy
level. This removes any choice of a density representative at energy zero. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedDensityContinuity
noncomputable section
open AxisProductDensity AxisDensityIntegrability L2ConvolutionContinuity
open MarkedProductDensity MarkedProductBounds
set_option maxHeartbeats 1000000

def markedSum (a : ℝ→ℝ≥0∞) (d1 d2 E : ℝ) : ℝ≥0∞ :=
  ∫⁻s:ℝ,∫⁻t:ℝ,a s*axisDensity d1 t*axisDensity d2 (E-s-t)

def realMarkedSum (a : ℝ→ℝ≥0∞) (d1 d2 E : ℝ) : ℝ :=
  ∫s:ℝ,(a s).toReal*(∫t:ℝ,(axisDensity d1 t).toReal*(axisDensity d2 (E-s-t)).toReal)

theorem marked_density_integrable {d : ℝ} (hd0 : 0≤d) (hd1 : d<1)
    {w : ℝ×ℝ→ℝ≥0∞} (hw : Measurable w) (hb : ∀p,w p≤1) :
    Integrable (fun t=>(productDensity (markedWeight d w) t).toReal) volume := by
  apply (axisDensity_real_integrable hd0 hd1.le).mono'
    (productDensity_measurable (markedWeight_measurable d hw)).ennreal_toReal.aestronglyMeasurable
  filter_upwards [marked_density_le_original hd0 hd1 w hb] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (axisDensity_finite d t).ne ht

theorem marked_density_finite_ae {d : ℝ} (hd0 : 0≤d) (hd1 : d<1)
    (w : ℝ×ℝ→ℝ≥0∞) (hb : ∀p,w p≤1) :
    ∀ᵐ t ∂(volume:Measure ℝ),productDensity (markedWeight d w) t≠∞ := by
  filter_upwards [marked_density_le_original hd0 hd1 w hb] with t ht
  exact (ht.trans_lt (axisDensity_finite d t)).ne

theorem realMarkedSum_continuous {a : ℝ→ℝ≥0∞}
    (ha : Integrable (fun t=>(a t).toReal) volume) {d1 d2 : ℝ}
    (h10 : 0≤d1) (h11 : d1≤1) (h20 : 0≤d2) (h21 : d2≤1) :
    Continuous (realMarkedSum a d1 d2) :=
  triple_convolution_continuous ha (axisDensity_real_memLp_two h10 h11)
    (axisDensity_real_memLp_two h20 h21)

theorem markedSum_eq_ofReal {a : ℝ→ℝ≥0∞}
    (ha : Integrable (fun t=>(a t).toReal) volume) (hfinite : ∀ᵐ t ∂volume,a t≠∞)
    {d1 d2 : ℝ} (h10 : 0≤d1) (h11 : d1≤1) (h20 : 0≤d2) (h21 : d2≤1) (E : ℝ) :
    markedSum a d1 d2 E=ENNReal.ofReal (realMarkedSum a d1 d2 E) := by
  have h1 := axisDensity_real_memLp_two h10 h11
  have h2 := axisDensity_real_memLp_two h20 h21
  have hinn (s : ℝ) : ENNReal.ofReal (∫t:ℝ,(axisDensity d1 t).toReal*
      (axisDensity d2 (E-s-t)).toReal)=∫⁻t:ℝ,axisDensity d1 t*axisDensity d2 (E-s-t) := by
    rw [ofReal_integral_eq_lintegral_ofReal (convolution_integrable h1 h2 (E-s))
      (ae_of_all _ (fun _=>mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (axisDensity_finite _ _).ne,ENNReal.ofReal_toReal (axisDensity_finite _ _).ne]
  have hp : ∀s,0≤(a s).toReal*(∫t:ℝ,(axisDensity d1 t).toReal*(axisDensity d2 (E-s-t)).toReal) :=
    fun _=>mul_nonneg ENNReal.toReal_nonneg
      (integral_nonneg (fun _=>mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
  unfold realMarkedSum
  rw [ofReal_integral_eq_lintegral_ofReal (triple_convolution_integrable ha h1 h2 E)
    (ae_of_all _ hp)]
  apply lintegral_congr_ae
  filter_upwards [hfinite] with s hs
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hs,hinn]
  have hm : Measurable (fun t:ℝ=>axisDensity d1 t*axisDensity d2 (E-s-t)) := by
    have := axisDensity_measurable d1
    have := axisDensity_measurable d2
    fun_prop
  rw [←lintegral_const_mul _ hm]
  apply lintegral_congr
  intro t
  ring

theorem actual_marked_sum_continuous {d0 d1 d2 : ℝ}
    (h00 : 0≤d0) (h01 : d0<1) (h10 : 0≤d1) (h11 : d1≤1)
    (h20 : 0≤d2) (h21 : d2≤1) {w : ℝ×ℝ→ℝ≥0∞}
    (hw : Measurable w) (hb : ∀p,w p≤1) :
    Continuous (markedSum (productDensity (markedWeight d0 w)) d1 d2) := by
  have hi := marked_density_integrable h00 h01 hw hb
  have hf := marked_density_finite_ae h00 h01 w hb
  have he := funext (markedSum_eq_ofReal hi hf h10 h11 h20 h21)
  rw [he]
  exact ENNReal.continuous_ofReal.comp (realMarkedSum_continuous hi h10 h11 h20 h21)

end
end Resonance.MarkedDensityContinuity
