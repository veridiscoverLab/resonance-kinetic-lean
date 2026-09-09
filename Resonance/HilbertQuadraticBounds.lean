import Resonance.RankTwoHilbert

/-! Explicit complex quadratic estimates for the compensation argument. -/
open InnerProductSpace ContinuousLinearMap
open scoped ComplexConjugate
namespace Resonance.HilbertQuadraticBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def quadratic (T : E→L[ℂ]E) (v : E) : ℝ := (inner ℂ v (T v)).re

theorem quadratic_add (T U : E→L[ℂ]E) (v : E) :
    quadratic (T+U) v=quadratic T v+quadratic U v := by
  simp only [quadratic,ContinuousLinearMap.add_apply,inner_add_right,Complex.add_re]

theorem quadratic_real_smul (a : ℝ) (T : E→L[ℂ]E) (v : E) :
    quadratic ((a:ℂ) • T) v=a*quadratic T v := by
  simp only [quadratic,ContinuousLinearMap.smul_apply,inner_smul_right,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem quadratic_neg (T : E→L[ℂ]E) (v : E) : quadratic (-T) v= -quadratic T v := by
  simp only [quadratic,ContinuousLinearMap.neg_apply,inner_neg_right,Complex.neg_re]

theorem pairing_bound (T : E→L[ℂ]E) (x y : E) :
    ‖inner ℂ x (T y)‖≤‖T‖*‖x‖*‖y‖ := by
  calc
    _ ≤ ‖x‖*‖T y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖*(‖T‖*‖y‖) := mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    _ = _ := by ring

theorem abs_quadratic_bound (T : E→L[ℂ]E) (v : E) :
    |quadratic T v|≤‖T‖*‖v‖^2 := by
  exact (Complex.abs_re_le_norm _).trans ((pairing_bound T v v).trans_eq (by ring))

theorem quadratic_sum_identity (T : E→L[ℂ]E) (e q : E) (t : ℂ) :
    quadratic T (t • e+q)=‖t‖^2*quadratic T e+
      (star t*inner ℂ e (T q)).re+(t*inner ℂ q (T e)).re+quadratic T q := by
  have ht : t*star t=((‖t‖^2:ℝ):ℂ) := by
    have hh := inner_self_eq_norm_sq_to_K (𝕜:=ℂ) t
    change t*star t=(‖t‖:ℂ)^2 at hh
    simpa only [Complex.ofReal_pow] using hh
  have hc : inner ℂ (t • e+q) (T (t • e+q))=
      ((‖t‖^2:ℝ):ℂ)*inner ℂ e (T e)+star t*inner ℂ e (T q)+
        t*inner ℂ q (T e)+inner ℂ q (T q) := by
    simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right]
    change t*(star t*inner ℂ e (T e)+inner ℂ q (T e))+
      (star t*inner ℂ e (T q)+inner ℂ q (T q))= _
    rw [←ht]
    ring
  have hh := congrArg Complex.re hc
  simpa only [quadratic,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using hh

theorem quadratic_sum_bound (T : E→L[ℂ]E) {e : E} (he : ‖e‖=1) (q : E) (t : ℂ) :
    quadratic T (t • e+q)≤‖t‖^2*quadratic T e+
      2*‖T‖*‖t‖*‖q‖+‖T‖*‖q‖^2 := by
  have hp := pairing_bound T e q
  have hq := pairing_bound T q e
  rw [he,mul_one] at hp hq
  have h1 : (star t*inner ℂ e (T q)).re≤‖t‖*(‖T‖*‖q‖) := by
    calc
      _ ≤ ‖star t*inner ℂ e (T q)‖ := Complex.re_le_norm _
      _ = ‖t‖*‖inner ℂ e (T q)‖ := by rw [norm_mul,norm_star]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
  have h2 : (t*inner ℂ q (T e)).re≤‖t‖*(‖T‖*‖q‖) := by
    calc
      _ ≤ ‖t*inner ℂ q (T e)‖ := Complex.re_le_norm _
      _ = ‖t‖*‖inner ℂ q (T e)‖ := norm_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
  have h3 := (le_abs_self (quadratic T q)).trans (abs_quadratic_bound T q)
  rw [quadratic_sum_identity]
  linarith

end
end Resonance.HilbertQuadraticBounds
