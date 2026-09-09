import Resonance.MarkedProductBounds

/-! Swap and addition identities for the original weighted product
pushforward; used before the full three-axis convolution. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedProductSymmetry
noncomputable section
open MarkedProductDensity MarkedProductBounds
set_option maxHeartbeats 1000000

theorem actual_product_swap {w : ℝ×ℝ→ℝ≥0∞} (hw : Measurable w) :
    productDensity (fun p=>w p.swap)=ᵐ[(volume:Measure ℝ)]productDensity w := by
  have hs : Measurable (fun p:ℝ×ℝ=>w p.swap) := hw.comp measurable_swap
  apply (withDensity_eq_iff_of_sigmaFinite (productDensity_measurable hs).aemeasurable
    (productDensity_measurable hw).aemeasurable).mp
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_withDensity_eq_lintegral_mul _ (productDensity_measurable hs) hF,
    lintegral_withDensity_eq_lintegral_mul _ (productDensity_measurable hw) hF]
  simp only [Pi.mul_apply]
  simp_rw [mul_comm (productDensity _ _) (F _)]
  rw [←actual_product_pushforward hs F hF,←actual_product_pushforward hw F hF]
  have hm : Measurable (fun p:ℝ×ℝ=>w p.swap*F (p.1*p.2)) := by fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  simp only [Prod.swap_prod_mk,mul_comm y x]

theorem actual_product_add {w v : ℝ×ℝ→ℝ≥0∞} (hw : Measurable w) (t : ℝ) :
    productDensity (fun p=>w p+v p) t=productDensity w t+productDensity v t := by
  unfold productDensity
  simp_rw [mul_add]
  exact lintegral_add_left (by fun_prop) _

theorem two_strip_density_bound (S : Set ℝ) (hS : MeasurableSet S) {L : ℝ}
    (hinv : ∀x∈S,|x⁻¹|≤L) {w : ℝ×ℝ→ℝ≥0∞}
    (hw : ∀p,w p≤S.indicator (fun _=>1) p.1+S.indicator (fun _=>1) p.2) :
    productDensity w≤ᵐ[(volume:Measure ℝ)]
      fun _=>2*(ENNReal.ofReal L*(volume:Measure ℝ) S) := by
  let v : ℝ×ℝ→ℝ≥0∞ := fun p=>S.indicator (fun _=>1) p.1
  have hv : Measurable v := (measurable_const.indicator hS).comp measurable_fst
  have hs := actual_product_swap hv
  filter_upwards [hs] with t ht
  calc
    _ ≤ productDensity (fun p=>v p+v p.swap) t := productDensity_mono hw t
    _ = productDensity v t+productDensity (fun p=>v p.swap) t :=
      actual_product_add hv t
    _ = 2*productDensity v t := by rw [ht]; ring
    _ ≤ _ := mul_le_mul_right
      (productDensity_strip_bound S hS v (fun _=>le_rfl) hinv t) 2

def productCut (δ : ℝ) (w : ℝ×ℝ→ℝ≥0∞) : ℝ×ℝ→ℝ≥0∞ :=
  {p | |p.1*p.2|≤δ}.indicator w

theorem productCut_density {δ t : ℝ} (ht : |t|≤δ) (w : ℝ×ℝ→ℝ≥0∞) :
    productDensity (productCut δ w) t=productDensity w t := by
  unfold productDensity
  apply lintegral_congr
  intro x
  by_cases hx:x=0
  · simp [hx]
  · have hp : (x,t/x)∈{p:ℝ×ℝ | |p.1*p.2|≤δ} := by
      simpa only [mem_setOf_eq,mul_div_cancel₀ t hx] using ht
    rw [productCut,indicator_of_mem hp]

end
end Resonance.MarkedProductSymmetry
