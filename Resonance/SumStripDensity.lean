import Resonance.SumStripGeometry

/-! A quantitative density bound on the physically allowed product
range, derived from the original marked product pushforward. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.SumStripDensity
noncomputable section
open MarkedProductDensity MarkedProductSymmetry SumStripGeometry
set_option maxHeartbeats 1200000

theorem cut_sum_strip_density_bound {a b l δ : ℝ} (hl : 0<l)
    (hfar : ∀s∈Icc a b,l≤|s|) {w : ℝ×ℝ→ℝ≥0∞} (hb : ∀p,w p≤1)
    (hs : ∀p,p.1+p.2∉Icc a b→w p=0) :
    productDensity (productCut δ w)≤ᵐ[(volume:Measure ℝ)]
      fun _=>ENNReal.ofReal (4/l)*ENNReal.ofReal (b-a+4*δ/l) := by
  have h := two_strip_density_bound (farStrip a b l δ) (farStrip_measurable a b l δ)
    (farStrip_inverse_bound a b δ hl) (marked_sum_strip_envelope hl hfar hb hs)
  filter_upwards [h] with t ht
  calc
    _ ≤ 2*(ENNReal.ofReal (2/l)*(volume:Measure ℝ) (farStrip a b l δ)) := ht
    _ ≤ 2*(ENNReal.ofReal (2/l)*ENNReal.ofReal (b-a+4*δ/l)) :=
      mul_le_mul_right (mul_le_mul_right (farStrip_volume_bound a b l δ) _) 2
    _ = _ := by
      rw [←mul_assoc,←ENNReal.ofReal_ofNat (n:=2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
      congr 2
      ring

theorem local_sum_strip_density_bound {a b l δ : ℝ} (hl : 0<l)
    (hfar : ∀s∈Icc a b,l≤|s|) {w : ℝ×ℝ→ℝ≥0∞} (hb : ∀p,w p≤1)
    (hs : ∀p,p.1+p.2∉Icc a b→w p=0) :
    ∀ᵐ t ∂(volume:Measure ℝ),|t|≤δ→productDensity w t≤
      ENNReal.ofReal (4/l)*ENNReal.ofReal (b-a+4*δ/l) := by
  filter_upwards [cut_sum_strip_density_bound hl hfar hb hs] with t ht hδ
  rwa [productCut_density hδ w] at ht

theorem original_local_sum_strip_bound (d : ℝ) {a b l δ : ℝ} (hl : 0<l)
    (hfar : ∀s∈Icc a b,l≤|s|) {w : ℝ×ℝ→ℝ}
    (hb : ∀p,w p≤1) (hs : ∀p,p.1+p.2∉Icc a b→w p=0) :
    ∀ᵐ t ∂(volume:Measure ℝ),|t|≤δ→
      productDensity (markedWeight d (fun p=>ENNReal.ofReal (w p))) t≤
        ENNReal.ofReal ((4/l)*(b-a+4*δ/l)) := by
  have hb' : ∀p,markedWeight d (fun p=>ENNReal.ofReal (w p)) p≤1 := by
    intro p
    by_cases hp:p∈CornerProductCoordinates.axisDomain d
    · rw [markedWeight,indicator_of_mem hp]
      exact ENNReal.ofReal_le_one.mpr (hb p)
    · simp only [markedWeight,indicator_of_notMem hp,zero_le]
  have hs' : ∀p,p.1+p.2∉Icc a b→markedWeight d (fun p=>ENNReal.ofReal (w p)) p=0 := by
    intro p hp
    by_cases hd:p∈CornerProductCoordinates.axisDomain d <;>
      simp [markedWeight,hd,hs p hp]
  have h := local_sum_strip_density_bound (δ:=δ) hl hfar hb' hs'
  rw [ENNReal.ofReal_mul (by positivity : 0≤4/l)]
  exact h

end
end Resonance.SumStripDensity
