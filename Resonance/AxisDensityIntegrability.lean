import Resonance.CornerLogKernels

/-! L¹ and L² of the actual signed-axis product density, including d=0.
This supplies the convolution-continuity bridge without selecting a value
of an arbitrary density representative at zero. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.AxisDensityIntegrability
noncomputable section
open Resonance.AxisProductDensity Resonance.CornerProductDensity
open Resonance.TriangleProductDensity Resonance.CornerDensityBounds Resonance.CornerLogKernels

theorem axisDensity_finite (d t:ℝ) : axisDensity d t<(∞:ℝ≥0∞) := by
  unfold axisDensity triangleDensity rectangleDensity
  split_ifs <;> simp
  all_goals exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

theorem axisDensity_zero_at_zero (d:ℝ) : axisDensity d 0=0 := by
  simp [axisDensity,triangleDensity,rectangleDensity]

theorem axisDensity_zero_outside {d t:ℝ} (hd0:0≤d) (hd1:d≤1) (ht:1≤|t|) :
    axisDensity d t=0 := by
  by_cases htp:0≤t
  · rw [abs_of_nonneg htp] at ht
    have hn : ¬0< -t := by linarith
    have ha : ¬t<d^2/4 := by nlinarith
    have hb : ¬t<(1-d)^2/4 := by nlinarith
    simp [axisDensity,triangleDensity,rectangleDensity,hn,ha,hb]
  · have htn : t≤0 := le_of_not_ge htp
    rw [abs_of_nonpos htn] at ht
    have hn : ¬0<t := not_lt.mpr htn
    have hz := rectangle_density_zero_of_large hd0 hd1 ht
    simp [axisDensity,triangleDensity,hn,hz]

theorem axisDensity_positive_bound {d t:ℝ} (hd0:0≤d) (hd1:d≤1) (ht:0<t) :
    axisDensity d t≤2*ENNReal.ofReal (logSize t) := by
  rw [axis_density_positive ht]
  have h1 := triangle_density_upper hd0 hd1 ht
  have h2 := triangle_density_upper (by linarith : 0≤1-d) (by linarith : 1-d≤1) ht
  have hl : Real.log (1/t)≤logSize t := by
    rw [one_div,Real.log_inv]
    dsimp [logSize]
    linarith [neg_le_abs (Real.log t)]
  calc
    _ ≤ ENNReal.ofReal (Real.log (1/t))+ENNReal.ofReal (Real.log (1/t)) := add_le_add h1 h2
    _ = 2*ENNReal.ofReal (Real.log (1/t)) := by ring
    _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal hl) 2

theorem axisDensity_negative_bound {d s:ℝ} (hd0:0≤d) (hd1:d≤1) (hs:0<s) :
    axisDensity d (-s)≤2*ENNReal.ofReal (logSize s) := by
  rw [axis_density_negative hs]
  have hl : Real.log (1/s)≤logSize s := by
    rw [one_div,Real.log_inv]
    dsimp [logSize]
    linarith [neg_le_abs (Real.log s)]
  exact mul_le_mul_right ((rectangle_density_upper hd0 hd1 hs).trans
    (ENNReal.ofReal_le_ofReal hl)) 2

def logMajorant (n:ℕ) : ℝ→ℝ := (Ioo (0:ℝ) 1).indicator (fun x=>(logSize x)^n)

theorem logMajorant_integrable (n:ℕ) (hn:n≤4) : Integrable (logMajorant n) volume :=
  (logSize_pow_integrable n hn).integrable_indicator measurableSet_Ioo

theorem axisDensity_power_integrable {d:ℝ} (hd0:0≤d) (hd1:d≤1)
    (n:ℕ) (hn0:0<n) (hn4:n≤4) :
    Integrable (fun t:ℝ=>(axisDensity d t).toReal^n) volume := by
  have hpos := logMajorant_integrable n hn4
  have hneg : Integrable (fun t:ℝ=>logMajorant n (-t)) volume :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hpos
  apply ((hpos.add hneg).const_mul ((2:ℝ)^n)).mono'
    ((axisDensity_measurable d).ennreal_toReal.pow_const n).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ENNReal.toReal_nonneg n)]
  by_cases hz:axisDensity d t=0
  · have hm (x:ℝ) : 0≤logMajorant n x := by
      by_cases hx:x∈Ioo (0:ℝ) 1
      · simpa [logMajorant,hx] using pow_nonneg (logSize_nonneg x) n
      · simp [logMajorant,hx]
    simp only [hz,ENNReal.toReal_zero,zero_pow hn0.ne']
    exact mul_nonneg (pow_nonneg (by norm_num) n) (add_nonneg (hm t) (hm (-t)))
  · have ht0 : t≠0 := by intro h;exact hz (h ▸ axisDensity_zero_at_zero d)
    have ht1 : |t|<1 := by
      by_contra h
      exact hz (axisDensity_zero_outside hd0 hd1 (le_of_not_gt h))
    by_cases hp:0<t
    · have ht : t∈Ioo (0:ℝ) 1 := ⟨hp,by simpa [abs_of_pos hp] using ht1⟩
      have hn : -t∉Ioo (0:ℝ) 1 := by intro hh; linarith [hh.1]
      have hbound := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top : 2*ENNReal.ofReal (logSize t)≠(∞:ℝ≥0∞))
        (axisDensity_positive_bound hd0 hd1 hp)
      have hbr : (axisDensity d t).toReal≤2*logSize t := by
        simpa [ENNReal.toReal_mul,ENNReal.toReal_ofReal (logSize_nonneg t)] using hbound
      simpa [logMajorant,Set.indicator_of_mem ht,Set.indicator_of_notMem hn,mul_pow] using
        pow_le_pow_left₀ ENNReal.toReal_nonneg hbr n
    · have hp' : 0< -t := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) ht0)
      have ht : -t∈Ioo (0:ℝ) 1 := ⟨hp',by simpa [abs_of_neg (neg_pos.mp hp')] using ht1⟩
      have hn : t∉Ioo (0:ℝ) 1 := by simp only [mem_Ioo]; tauto
      have hb0 := axisDensity_negative_bound hd0 hd1 hp'
      rw [neg_neg] at hb0
      have hbound := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top : 2*ENNReal.ofReal (logSize (-t))≠(∞:ℝ≥0∞)) hb0
      have hbr : (axisDensity d t).toReal≤2*logSize (-t) := by
        simpa [ENNReal.toReal_mul,ENNReal.toReal_ofReal (logSize_nonneg (-t))] using hbound
      simpa [logMajorant,Set.indicator_of_mem ht,Set.indicator_of_notMem hn,mul_pow] using
        pow_le_pow_left₀ ENNReal.toReal_nonneg hbr n

theorem axisDensity_real_integrable {d:ℝ} (hd0:0≤d) (hd1:d≤1) :
    Integrable (fun t=>(axisDensity d t).toReal) volume := by
  simpa using axisDensity_power_integrable hd0 hd1 1 (by norm_num) (by norm_num)

theorem axisDensity_real_memLp_two {d:ℝ} (hd0:0≤d) (hd1:d≤1) :
    MemLp (fun t=>(axisDensity d t).toReal) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (axisDensity_measurable d).ennreal_toReal.aestronglyMeasurable).mpr
  simpa [Real.norm_eq_abs,sq_abs] using
    axisDensity_power_integrable hd0 hd1 2 (by norm_num) (by norm_num)

end
end Resonance.AxisDensityIntegrability
