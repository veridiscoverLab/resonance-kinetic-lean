import Resonance.AxisProductDensity

open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerDensityBounds
noncomputable section
set_option maxHeartbeats 600000
open Resonance.CornerProductDensity Resonance.TriangleProductDensity

/-- Uniform in b∈[1/2,1], including the unchanged-coordinate limit b=1.
These are bounds on the proved original triangular product density. -/
theorem small_triangle_density_bounds {b t:ℝ} (hb0:(1:ℝ)/2≤b) (hb1:b≤1)
    (ht:0<t) (hts:t≤(1:ℝ)/256) :
    ENNReal.ofReal (Real.log (1/t)/2)≤triangleDensity b t ∧
      triangleDensity b t≤ENNReal.ofReal (Real.log (1/t)) := by
  have hb : 0<b := by linarith
  have htop : t<b^2/4 := by nlinarith
  have hd : 0≤b^2-4*t := by linarith
  have hs0 := Real.sqrt_nonneg (b^2-4*t)
  have hs2 := Real.sq_sqrt hd
  have hsb : Real.sqrt (b^2-4*t)≤b := by nlinarith
  have huN : (b+Real.sqrt (b^2-4*t))^2≤4 := by nlinarith
  have hlN : (1:ℝ)/4≤(b+Real.sqrt (b^2-4*t))^2 := by nlinarith
  let z : ℝ := (b+Real.sqrt (b^2-4*t))^2/(4*t)
  have hz : 0<z := by dsimp [z]; positivity
  have hzu : z≤1/t := by
    apply (div_le_div_iff₀ (by positivity) ht).mpr
    nlinarith [mul_le_mul_of_nonneg_right huN ht.le]
  have hzl : 1/(16*t)≤z := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlN ht.le]
  have hi : 1/t≤(1/(16*t))^2 := by
    rw [show (1/(16*t))^2=1/(256*t^2) by ring]
    apply (div_le_div_iff₀ ht (by positivity)).mpr
    have hn : 0≤1-256*t := by linarith
    nlinarith [mul_nonneg ht.le hn]
  have hiz : 1/t≤z^2 := hi.trans (by
    have hl0 : 0≤1/(16*t) := by positivity
    nlinarith)
  have huLog := Real.log_le_log hz hzu
  have hlLog := Real.log_le_log (by positivity : 0<1/t) hiz
  rw [Real.log_pow] at hlLog
  norm_num at hlLog
  rw [triangleDensity,if_pos ⟨ht,htop⟩]
  constructor
  · exact ENNReal.ofReal_le_ofReal (by
      change Real.log (1/t)/2≤Real.log z
      rw [one_div,Real.log_inv]
      linarith)
  · exact ENNReal.ofReal_le_ofReal huLog

theorem rectangle_density_upper {d e s:ℝ} (hd0:0≤d)
    (hde:d≤e) (hs:0<s) :
    rectangleDensity d (1-d) s≤ENNReal.ofReal (Real.log (e/s)) := by
  by_cases htop:s<d*(1-d)
  · have hp : 0<d*(1-d)/s := div_pos (hs.trans htop) hs
    have hab : d*(1-d)≤e := by nlinarith
    rw [rectangleDensity,if_pos ⟨hs,htop⟩]
    exact ENNReal.ofReal_le_ofReal (Real.log_le_log hp ((div_le_div_iff_of_pos_right hs).mpr hab))
  · simp [rectangleDensity,htop]

/-- The coordinate attaining the maximum corner distance supplies a
fixed positive negative-product density on an interval of length O(e). -/
theorem rectangle_density_lower_on_corner_band {e s:ℝ}
    (he:0<e) (hes:e≤(1:ℝ)/2) (hs0:0<s) (hs1:s≤e/4) :
    ENNReal.ofReal (Real.log 2)≤rectangleDensity e (1-e) s := by
  have hab : e/2≤e*(1-e) := by nlinarith
  have htop : s<e*(1-e) := by linarith
  have hlo : (2:ℝ)≤e*(1-e)/s := (le_div_iff₀ hs0).mpr (by linarith)
  rw [rectangleDensity,if_pos ⟨hs0,htop⟩]
  exact ENNReal.ofReal_le_ofReal (Real.log_le_log (by norm_num) hlo)

/-- The small-side triangle has the same global logarithmic upper bound;
no lower bound on its side length is required. -/
theorem triangle_density_upper {b t:ℝ} (hb0:0≤b) (hb1:b≤1) (ht:0<t) :
    triangleDensity b t≤ENNReal.ofReal (Real.log (1/t)) := by
  by_cases htop:t<b^2/4
  · have hd : 0≤b^2-4*t := by linarith
    have hs0 := Real.sqrt_nonneg (b^2-4*t)
    have hs2 := Real.sq_sqrt hd
    have hsb : Real.sqrt (b^2-4*t)≤b := by nlinarith
    have hnum : (b+Real.sqrt (b^2-4*t))^2≤4 := by nlinarith
    have hb : 0<b := by nlinarith
    have hz : 0<(b+Real.sqrt (b^2-4*t))^2/(4*t) := by positivity
    have hratio : (b+Real.sqrt (b^2-4*t))^2/(4*t)≤1/t := by
      apply (div_le_div_iff₀ (by positivity) ht).mpr
      nlinarith [mul_le_mul_of_nonneg_right hnum ht.le]
    rw [triangleDensity,if_pos ⟨ht,htop⟩]
    exact ENNReal.ofReal_le_ofReal (Real.log_le_log hz hratio)
  · simp [triangleDensity,htop]

theorem rectangle_density_zero_of_large {d e s:ℝ} (hd0:0≤d)
    (hde:d≤e) (hes:e ≤ s) : rectangleDensity d (1-d) s=0 := by
  have hab : d*(1-d) ≤ s := by nlinarith
  simp [rectangleDensity,not_lt.mpr hab]

theorem axis_density_positive {d t:ℝ} (ht:0<t) :
    AxisProductDensity.axisDensity d t=triangleDensity d t+triangleDensity (1-d) t := by
  have hn : ¬0< -t := by linarith
  simp [AxisProductDensity.axisDensity,rectangleDensity,hn]

theorem axis_density_negative {d s:ℝ} (hs:0<s) :
    AxisProductDensity.axisDensity d (-s)=2*rectangleDensity d (1-d) s := by
  have hn : ¬0< -s := by linarith
  simp [AxisProductDensity.axisDensity,triangleDensity,hn]

end
end Resonance.CornerDensityBounds
