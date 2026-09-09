import Resonance.MarkedProductBounds

/-! The full resonance relation itself restricts every marked product
to twice the largest original deficit. This truncation is derived inside
the complete convolution and does not discard a collision sign pattern. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedConvolutionSupport
noncomputable section
open AxisProductDensity CornerDensityBounds CornerConvolutionSigns CornerConvolutionBounds
open MarkedCornerConvolution CornerZeroBounds CornerLogKernels

theorem axisDensity_vanish_below {d e t : ℝ} (hd : 0≤d) (hde : d≤e)
    (he : 0<e) (ht : t≤-e) : axisDensity d t=0 := by
  have hn : 0< -t := by linarith
  have hh := axis_density_negative (d:=d) hn
  rw [neg_neg] at hh
  rw [hh,CornerDensityBounds.rectangle_density_zero_of_large hd hde (by linarith)]
  simp

def truncateAxis (e : ℝ) (a : ℝ→ℝ≥0∞) : ℝ→ℝ≥0∞ :=
  (Icc (-2*e) (2*e)).indicator a

theorem tripleZero_original_support {d0 d1 d2 e : ℝ} (he : 0<e)
    (h00 : 0≤d0) (h0e : d0≤e) (h10 : 0≤d1) (h1e : d1≤e)
    (h20 : 0≤d2) (h2e : d2≤e) (a : ℝ→ℝ≥0∞)
    (ha : a≤ᵐ[(volume:Measure ℝ)]axisDensity d0) :
    tripleZero a (axisDensity d1) (axisDensity d2)=
      tripleZero (truncateAxis e a) (axisDensity d1) (axisDensity d2) := by
  apply lintegral_congr_ae
  filter_upwards [ha] with s hs
  apply lintegral_congr
  intro t
  by_cases hi:s∈Icc (-2*e) (2*e)
  · rw [truncateAxis,indicator_of_mem hi]
  · rw [truncateAxis,indicator_of_notMem hi,zero_mul,zero_mul]
    by_cases hlow:s< -2*e
    · have hz := axisDensity_vanish_below h00 h0e he (by linarith:s≤-e)
      have ha0 : a s=0 := le_antisymm (hs.trans_eq hz) (zero_le _)
      rw [ha0,zero_mul,zero_mul]
    · have hhigh : 2*e<s := by
        have hleft : -2*e ≤ s := le_of_not_gt hlow
        exact lt_of_not_ge (fun hright=>hi ⟨hleft,hright⟩)
      by_cases ht:t≤-e
      · rw [axisDensity_vanish_below h10 h1e he ht,mul_zero,zero_mul]
      · rw [axisDensity_vanish_below h20 h2e he (by linarith:-s-t≤-e),mul_zero]

theorem original_marked_convolution_bound {d0 d1 d2 e : ℝ} (he : 0<e)
    (he1 : e≤(1:ℝ)/4096) (h00 : 0≤d0) (h0e : d0≤e)
    (h10 : 0≤d1) (h1e : d1≤e) (h20 : 0≤d2) (h2e : d2≤e)
    (B : ℝ≥0∞) (a : ℝ→ℝ≥0∞) (hb : ∀t,a t≤B)
    (ha : a≤ᵐ[(volume:Measure ℝ)]axisDensity d0) :
    tripleZero a (axisDensity d1) (axisDensity d2)≤
      (64*(B/ENNReal.ofReal (Real.log 2))*upperCoefficient)*
        (ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2 := by
  rw [tripleZero_original_support he h00 h0e h10 h1e h20 h2e a ha]
  apply bounded_marked_convolution he he1 h10 h1e h20 h2e B
  · intro t
    by_cases ht:t∈Icc (-2*e) (2*e)
    · simpa only [truncateAxis,indicator_of_mem ht] using hb t
    · simp only [truncateAxis,indicator_of_notMem ht,zero_le]
  · intro t ht
    have hn : t∉Icc (-2*e) (2*e) := by
      intro hi
      have hab : |t|≤2*e := abs_le.mpr ⟨by linarith [hi.1],hi.2⟩
      linarith
    exact indicator_of_notMem hn a

end
end Resonance.MarkedConvolutionSupport
