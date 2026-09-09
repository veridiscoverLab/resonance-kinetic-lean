import Resonance.CornerZeroBounds

/-! A marked product density is dominated by an actual enlarged-corner
axis density. This is used inside the same full zero-energy convolution
to prove small conditional masses for incompatible collision roles. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedAxisDomination
noncomputable section
open AxisProductDensity CornerDensityBounds CornerZeroBounds
open CornerConvolution CornerConvolutionSigns CornerConvolutionBounds

theorem enlarged_axis_lower {e t : ℝ} (he : 0<e) (he1 : e≤(1:ℝ)/4096)
    (ht : t≠0) (hte : |t|≤2*e) :
    ENNReal.ofReal (Real.log 2)≤axisDensity (8*e) t := by
  by_cases hp : 0<t
  · have hl := (small_triangle_density_bounds (b:=1-8*e)
      (by linarith) (by linarith) hp (by rw [abs_of_pos hp] at hte; linarith)).1
    have ht4 : t≤(1:ℝ)/4 := by rw [abs_of_pos hp] at hte; linarith
    have hlog := Real.log_le_log (by norm_num:(0:ℝ)<4)
      ((le_div_iff₀ hp).mpr (by linarith:4*t≤1))
    have heq : Real.log (4:ℝ)=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    rw [heq] at hlog
    rw [axis_density_positive hp]
    exact ((ENNReal.ofReal_le_ofReal (by linarith)).trans hl).trans le_add_self
  · have hn : 0< -t := by rcases lt_or_gt_of_ne ht with h|h <;> linarith
    have hs : -t≤(8*e)/4 := by rw [abs_of_neg (by linarith)] at hte; linarith
    have hl := rectangle_density_lower_on_corner_band (e:=8*e) (by positivity)
      (by linarith) hn hs
    have hd := axis_density_negative (d:=8*e) hn
    rw [neg_neg] at hd
    rw [hd]
    exact hl.trans (le_mul_of_one_le_left' (by norm_num))

theorem bounded_marked_axis_domination {e : ℝ} (he : 0<e)
    (he1 : e≤(1:ℝ)/4096) (B : ℝ≥0∞) (a : ℝ→ℝ≥0∞)
    (hb : ∀t,a t≤B) (hs : ∀t,2*e < |t| → a t=0) :
    ∀ᵐ t ∂(volume:Measure ℝ),
      a t≤(B/(ENNReal.ofReal (Real.log 2)))*axisDensity (8*e) t := by
  filter_upwards [(volume:Measure ℝ).ae_ne 0] with t ht
  by_cases hte : |t|≤2*e
  · have hl := enlarged_axis_lower he he1 ht hte
    have hL : ENNReal.ofReal (Real.log 2)≠0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num)))
    calc
      a t ≤ B := hb t
      _ = (B/ENNReal.ofReal (Real.log 2))*ENNReal.ofReal (Real.log 2) :=
        (ENNReal.div_mul_cancel hL ENNReal.ofReal_ne_top).symm
      _ ≤ _ := mul_le_mul_right hl _
  · rw [hs t (lt_of_not_ge hte)]
    exact zero_le _

end
end Resonance.MarkedAxisDomination
