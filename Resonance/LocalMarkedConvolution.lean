import Resonance.MarkedRelativeMass

/-! The bounded-axis replacement only needs the density bound on the
product range forced by the original complete resonance constraint. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.LocalMarkedConvolution
noncomputable section
open AxisProductDensity CornerConvolution CornerConvolutionSigns
open CornerZeroBounds CornerLogKernels MarkedConvolutionSupport MarkedCornerConvolution
open MarkedDensityContinuity MarkedRelativeMass
set_option maxHeartbeats 1200000

theorem original_local_convolution_bound {d0 d1 d2 e : ℝ} (he : 0<e)
    (he1 : e≤(1:ℝ)/4096) (h00 : 0≤d0) (h0e : d0≤e)
    (h10 : 0≤d1) (h1e : d1≤e) (h20 : 0≤d2) (h2e : d2≤e)
    (B : ℝ≥0∞) (a : ℝ→ℝ≥0∞)
    (hb : ∀ᵐ t ∂(volume:Measure ℝ),|t|≤2*e→a t≤B)
    (ha : a≤ᵐ[(volume:Measure ℝ)]axisDensity d0) :
    tripleZero a (axisDensity d1) (axisDensity d2)≤
      (64*(B/ENNReal.ofReal (Real.log 2))*upperCoefficient)*
        (ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2 := by
  rw [tripleZero_original_support he h00 h0e h10 h1e h20 h2e a ha]
  have heq : truncateAxis e a=ᵐ[(volume:Measure ℝ)]fun t=>min (truncateAxis e a t) B := by
    filter_upwards [hb] with t ht
    by_cases hi:t∈Icc (-2*e) (2*e)
    · rw [truncateAxis,indicator_of_mem hi,min_eq_left]
      exact ht (abs_le.mpr ⟨by linarith [hi.1],hi.2⟩)
    · rw [truncateAxis,indicator_of_notMem hi,min_eq_left (zero_le _)]
  have hreplace : tripleZero (truncateAxis e a) (axisDensity d1) (axisDensity d2)=
      tripleZero (fun t=>min (truncateAxis e a t) B) (axisDensity d1) (axisDensity d2) := by
    apply lintegral_congr_ae
    filter_upwards [heq] with s hs
    apply lintegral_congr
    intro t
    exact congrArg (fun v=>v*axisDensity d1 t*axisDensity d2 (-s-t)) hs
  rw [hreplace]
  apply bounded_marked_convolution he he1 h10 h1e h20 h2e B
  · exact fun t=>min_le_right _ _
  · intro t ht
    have hn : t∉Icc (-2*e) (2*e) := by
      intro hi
      have h := abs_le.mpr ⟨by linarith [hi.1],hi.2⟩
      linarith
    rw [truncateAxis,indicator_of_notMem hn,min_eq_left (zero_le _)]

theorem original_local_real_bound {d : Fin 3→ℝ} {e B : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hB : 0≤B) (a : ℝ→ℝ≥0∞)
    (hb : ∀ᵐ t ∂(volume:Measure ℝ),|t|≤2*e→a t≤ENNReal.ofReal B)
    (ha : a≤ᵐ[(volume:Measure ℝ)]axisDensity (d 0)) :
    (markedSum a (d 1) (d 2) 0).toReal≤
      64*(B/Real.log 2)*upperCoefficient.toReal*e^2*(logSize e)^2 := by
  have hlog : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hu := original_local_convolution_bound he he1 (hd0 0) (hde 0) (hd0 1) (hde 1)
    (hd0 2) (hde 2) (ENNReal.ofReal B) a hb ha
  have hc : ((64*(ENNReal.ofReal B/ENNReal.ofReal (Real.log 2))*upperCoefficient)*
      (ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2)≠∞ := by
    have hden : ENNReal.ofReal (Real.log 2)≠0 := (ENNReal.ofReal_pos.mpr hlog).ne'
    have hdiv : ENNReal.ofReal B/ENNReal.ofReal (Real.log 2)≠∞ :=
      ENNReal.div_ne_top ENNReal.ofReal_ne_top hden
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hdiv)) upperCoefficient_finite)
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)).ne
  have ht := ENNReal.toReal_mono hc hu
  simpa only [markedSum,tripleZero,zero_sub,
    ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hB,ENNReal.toReal_ofReal hlog.le,
    ENNReal.toReal_ofReal he.le,ENNReal.toReal_ofReal (logSize_nonneg e)] using ht

theorem original_local_relative_bound {d : Fin 3→ℝ} {e B : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hmax : ∃i,d i=e) (hB : 0≤B) (a : ℝ→ℝ≥0∞)
    (hb : ∀ᵐ t ∂(volume:Measure ℝ),|t|≤2*e→a t≤ENNReal.ofReal B)
    (ha : a≤ᵐ[(volume:Measure ℝ)]axisDensity (d 0)) :
    (markedSum a (d 1) (d 2) 0).toReal≤relativeConstant*B*(sumDensity d 0).toReal := by
  have hm := original_local_real_bound he he1 hd0 hde hB a hb ha
  have hl := (sumDensity_zero_two_sided d hd0 hde hmax he (by linarith)).1
  have hlog := logSize_corner_bound he (by linarith)
  have hs : (logSize e)^2≤4*(Real.log (1/e))^2 := by nlinarith [logSize_nonneg e]
  have hp : 0≤64*(B/Real.log 2)*upperCoefficient.toReal*e^2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg hB (Real.log_nonneg (by norm_num)))) ENNReal.toReal_nonneg) (sq_nonneg e)
  calc
    _ ≤ 64*(B/Real.log 2)*upperCoefficient.toReal*e^2*(logSize e)^2 := hm
    _ ≤ 64*(B/Real.log 2)*upperCoefficient.toReal*e^2*(4*(Real.log (1/e))^2) :=
      mul_le_mul_of_nonneg_left hs hp
    _ = relativeConstant*B*(lowerConstant*e^2*(Real.log (1/e))^2) := by
      unfold relativeConstant
      field_simp [lowerConstant_pos.ne', (Real.log_pos (by norm_num : (1:ℝ)<2)).ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg relativeConstant_nonneg hB)

end
end Resonance.LocalMarkedConvolution
