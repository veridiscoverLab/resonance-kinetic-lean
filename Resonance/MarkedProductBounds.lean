import Resonance.MarkedProductDensity
import Resonance.CollisionFrequencyConvolution

/-! Actual marked polygon densities: domination by the original axis
law and a sharp width bound for a strip away from the product axis. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedProductBounds
noncomputable section
open CornerProductCoordinates AxisProductDensity MarkedProductDensity
set_option maxHeartbeats 1000000

theorem productDensity_mono {w v : ℝ×ℝ→ℝ≥0∞} (h : ∀p,w p≤v p) (t : ℝ) :
    productDensity w t≤productDensity v t := by
  exact lintegral_mono (fun x=>mul_le_mul' le_rfl (h (x,t/x)))

theorem unmarked_density_ae {d : ℝ} (hd0 : 0≤d) (hd1 : d<1) :
    productDensity (markedWeight d (fun _=>1))=ᵐ[(volume:Measure ℝ)]axisDensity d := by
  apply (withDensity_eq_iff_of_sigmaFinite
    (productDensity_measurable (markedWeight_measurable d measurable_const)).aemeasurable
    (axisDensity_measurable d).aemeasurable).mp
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_withDensity_eq_lintegral_mul _
    (productDensity_measurable (markedWeight_measurable d measurable_const)) hF,
    lintegral_withDensity_eq_lintegral_mul _ (axisDensity_measurable d) hF]
  have h1 := actual_marked_polygon_density d (w:=fun _=>1) measurable_const F hF
  simp only [one_mul] at h1
  simpa only [mul_comm] using h1.symm.trans (full_axis_product_lintegral hd0 hd1 F hF)

theorem marked_density_le_original {d : ℝ} (hd0 : 0≤d) (hd1 : d<1)
    (w : ℝ×ℝ→ℝ≥0∞) (hw : ∀p,w p≤1) :
    productDensity (markedWeight d w)≤ᵐ[(volume:Measure ℝ)]axisDensity d := by
  filter_upwards [unmarked_density_ae hd0 hd1] with t ht
  rw [←ht]
  apply productDensity_mono
  intro p
  by_cases hp:p∈axisDomain d
  · simpa only [markedWeight,indicator_of_mem hp] using hw p
  · simp only [markedWeight,indicator_of_notMem hp,le_refl]

theorem productDensity_strip_bound (S : Set ℝ) (hS : MeasurableSet S)
    {L : ℝ} (w : ℝ×ℝ→ℝ≥0∞)
    (hw : ∀p,w p≤S.indicator (fun _=>1) p.1)
    (hinv : ∀x∈S,|x⁻¹|≤L) (t : ℝ) :
    productDensity w t≤ENNReal.ofReal L*(volume:Measure ℝ) S := by
  have hpoint (x : ℝ) : ENNReal.ofReal (|x⁻¹|)*w (x,t/x)≤
      S.indicator (fun _=>ENNReal.ofReal L) x := by
    by_cases hx:x∈S
    · rw [indicator_of_mem hx]
      have h := hw (x,t/x)
      rw [indicator_of_mem hx] at h
      exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (hinv x hx)) h).trans_eq (mul_one _)
    · have h := hw (x,t/x)
      rw [indicator_of_notMem hx] at h
      have hz : w (x,t/x)=0 := le_antisymm h (zero_le _)
      rw [hz,mul_zero,indicator_of_notMem hx]
  apply (lintegral_mono hpoint).trans_eq
  rw [lintegral_indicator hS,lintegral_const,Measure.restrict_apply_univ]

theorem far_strip_inverse_bound {l a b : ℝ} (hl : 0<l)
    (hfar : ∀x∈Icc a b,l≤|x|) : ∀x∈Icc a b,|x⁻¹|≤l⁻¹ := by
  intro x hx
  rw [abs_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hl (hfar x hx)

theorem marked_far_strip_bound (d : ℝ) {l a b : ℝ} (hl : 0<l)
    (hfar : ∀x∈Icc a b,l≤|x|) (t : ℝ) :
    productDensity (markedWeight d (fun p=>(Icc a b).indicator (fun _=>1) p.1)) t≤
      ENNReal.ofReal (l⁻¹)*ENNReal.ofReal (b-a) := by
  have h := productDensity_strip_bound (Icc a b) measurableSet_Icc
    (markedWeight d (fun p=>(Icc a b).indicator (fun _=>1) p.1))
    (by
      intro p
      by_cases hp:p∈axisDomain d <;> simp [markedWeight,hp])
    (far_strip_inverse_bound hl hfar) t
  simpa only [Real.volume_Icc] using h

end
end Resonance.MarkedProductBounds
