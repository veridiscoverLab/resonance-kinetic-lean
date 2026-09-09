import Resonance.CornerDensityBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Integrable universal logarithmic majorants for the six actual product
signs. These estimates are independent of the three corner distances. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CornerLogKernels
noncomputable section

def logSize (x:ℝ) : ℝ := 1+|Real.log x|

theorem logSize_nonneg (x:ℝ) : 0≤logSize x := by dsimp [logSize]; positivity

theorem logSize_ge_one (x:ℝ) : 1≤logSize x := by dsimp [logSize]; linarith [abs_nonneg (Real.log x)]

theorem logSize_eq {x:ℝ} (hx0:0<x) (hx1:x≤1) : logSize x=1-Real.log x := by
  rw [logSize,abs_of_nonpos (Real.log_nonpos hx0.le hx1)]
  ring

theorem logSize_mul_le (x y:ℝ) (hx:x≠0) (hy:y≠0) :
    logSize (x*y)≤logSize x*logSize y := by
  rw [logSize,Real.log_mul hx hy]
  have ht := abs_add_le (Real.log x) (Real.log y)
  dsimp [logSize]
  nlinarith [mul_nonneg (abs_nonneg (Real.log x)) (abs_nonneg (Real.log y))]

theorem logSize_small_bound {x:ℝ} (hx0:0<x) (hx1:x≤1) :
    logSize x≤17*x^(-(1:ℝ)/16) := by
  have hl := Real.log_le_rpow_div (inv_nonneg.mpr hx0.le) (by norm_num : (0:ℝ)<1/16)
  rw [Real.log_inv,Real.inv_rpow hx0.le,←Real.rpow_neg hx0.le] at hl
  have hr : 1≤x^(-(1:ℝ)/16) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by norm_num)
  rw [logSize_eq hx0 hx1]
  norm_num at hl
  linarith

theorem logSize_pow_integrable (n:ℕ) (hn:n≤4) :
    IntegrableOn (fun x:ℝ=>(logSize x)^n) (Ioo 0 1) volume := by
  have hnR : (n:ℝ)≤4 := by exact_mod_cast hn
  have hr : -1< -(n:ℝ)/16 := by linarith
  have hi : IntegrableOn (fun x:ℝ=>x^(-(n:ℝ)/16)) (Ioo 0 1) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr hr
  apply (hi.const_mul ((17:ℝ)^n)).mono' (by unfold logSize; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (logSize_nonneg x) n)]
  calc
    _ ≤ (17*x^(-(1:ℝ)/16))^n := pow_le_pow_left₀ (logSize_nonneg x) (logSize_small_bound hx.1 hx.2.le) n
    _ = 17^n*x^(-(n:ℝ)/16) := by
      rw [mul_pow,←Real.rpow_mul_natCast hx.1.le]
      congr 1
      congr 1
      ring

def logMoment (n:ℕ) : ℝ≥0∞ := ∫⁻x in Ioo (0:ℝ) 1,ENNReal.ofReal ((logSize x)^n)

theorem logMoment_finite (n:ℕ) (hn:n≤4) : logMoment n<(∞:ℝ≥0∞) := by
  have hi := logSize_pow_integrable n hn
  unfold logMoment
  rw [←ofReal_integral_eq_lintegral_ofReal hi]
  · exact ENNReal.ofReal_lt_top
  · exact Eventually.of_forall (fun x=>pow_nonneg (logSize_nonneg x) n)

theorem scale_unit_lintegral {s:ℝ} (hs:0<s) (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioo 0 s,F x)=ENNReal.ofReal s*(∫⁻u in Ioo (0:ℝ) 1,F (s*u)) := by
  have him : (fun u:ℝ=>s*u) '' Ioo (0:ℝ) 1=Ioo 0 s := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨mul_pos hs hu.1,by nlinarith [hu.2]⟩
    · intro hx
      refine ⟨x/s,⟨div_pos hx.1 hs,(div_lt_one hs).mpr hx.2⟩,?_⟩
      field_simp
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s:=Ioo (0:ℝ) 1) (f:=fun u:ℝ=>s*u)
    (f':=fun _=>s) measurableSet_Ioo
    (fun u _=>by simpa using ((hasDerivAt_id u).const_mul s).hasDerivWithinAt)
    (fun u _ v _ huv=>(mul_left_cancel₀ hs.ne' huv)) F
  rw [him] at hcv
  rw [abs_of_pos hs] at hcv
  exact hcv.trans (lintegral_const_mul (ENNReal.ofReal s)
    (show Measurable (fun u:ℝ=>F (s*u)) from hF.comp (measurable_const_mul s)))

theorem reflect_unit_lintegral (F:ℝ→ℝ≥0∞) :
    (∫⁻u in Ioo (0:ℝ) 1,F (1-u))=∫⁻u in Ioo (0:ℝ) 1,F u := by
  have him : (fun u:ℝ=>1-u) '' Ioo (0:ℝ) 1=Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      constructor <;> linarith [hu.1,hu.2]
    · intro hx
      exact ⟨1-x,⟨by linarith [hx.2],by linarith [hx.1]⟩,by ring⟩
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s:=Ioo (0:ℝ) 1) (f:=fun u:ℝ=>1-u)
    (f':=fun _=> -1) measurableSet_Ioo
    (fun u _=>by simpa using ((hasDerivAt_id u).const_sub 1).hasDerivWithinAt)
    (fun u _ v _ huv=>by linarith) F
  rw [him] at hcv
  simpa using hcv.symm

end
end Resonance.CornerLogKernels
