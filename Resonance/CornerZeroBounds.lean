import Resonance.CornerConvolutionSigns
import Resonance.CornerConvolutionLower

/-! Uniform complete-convolution bounds, including directions for which
one or two coordinate deficits vanish. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerZeroBounds
noncomputable section
set_option maxHeartbeats 800000
open Resonance.CornerConvolution Resonance.CornerConvolutionBounds
open Resonance.CornerConvolutionSigns Resonance.CornerConvolutionLower
open Resonance.CornerLogKernels

def upperCoefficient : ℝ≥0∞ :=
  48*logMoment 2*logMoment 3+24*logMoment 2*logMoment 1

theorem upperCoefficient_finite : upperCoefficient<∞ := by
  unfold upperCoefficient
  have h1 := logMoment_finite 1 (by norm_num)
  have h2 := logMoment_finite 2 (by norm_num)
  have h3 := logMoment_finite 3 (by norm_num)
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) h2) h3,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) h2) h1⟩

theorem sumDensity_zero_upper (d:Fin 3→ℝ) {e:ℝ}
    (hd0:∀i,0≤d i) (hde:∀i,d i≤e) (hd1:∀i,d i≤1) (he:0<e) :
    sumDensity d 0≤upperCoefficient*(ENNReal.ofReal e)^2*
      (ENNReal.ofReal (logSize e))^2 := by
  have hL : ENNReal.ofReal (logSize e)≤(ENNReal.ofReal (logSize e))^2 := by
    have hr : logSize e≤(logSize e)^2 := by nlinarith [logSize_ge_one e]
    rw [←ENNReal.ofReal_pow (logSize_nonneg e)]
    exact ENNReal.ofReal_le_ofReal hr
  have hO (j i l:Fin 3) := one_negative_upper (hd0 j) (hde j) (hd0 i) (hd1 i)
    (hd0 l) (hd1 l) he
  have hT (i l j:Fin 3) : twoNegative (d i) (d l) (d j)≤
      8*(ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2*logMoment 2*logMoment 1 := by
    apply (two_negative_upper (hd0 i) (hde i) (hd0 l) (hde l) (hd0 j) (hd1 j) he).trans
    gcongr
  rw [sumDensity_six_signs]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (hO 0 1 2) (hO 1 0 2)) (hO 2 0 1)) (hT 0 1 2)) (hT 0 2 1))
    (hT 1 2 0)).trans_eq (by unfold upperCoefficient; ring)

theorem sumDensity_cycle_left (d:Fin 3→ℝ) :
    sumDensity d 0=sumDensity ![d 1,d 2,d 0] 0 := by
  calc
    _ = sumDensity ![d 2,d 0,d 1] 0 := sumDensity_rotate d
    _ = _ := by simpa using sumDensity_rotate ![d 2,d 0,d 1]

theorem sumDensity_zero_lower (d:Fin 3→ℝ) {e:ℝ}
    (hd0:∀i,0≤d i) (hde:∀i,d i≤e) (hmax:∃i,d i=e)
    (he0:0<e) (he1:e≤(1:ℝ)/256) :
    (ENNReal.ofReal (Real.log (1/e)/2))^2*(2*ENNReal.ofReal (Real.log 2))*
      (ENNReal.ofReal (e/48))^2≤ sumDensity d 0 := by
  obtain ⟨i,hi⟩ := hmax
  fin_cases i
  · rw [sumDensity_cycle_left]
    apply third_max_lower ![d 1,d 2,d 0] _ _ (by simpa using hi) he0 he1
    · intro j; fin_cases j
      · exact hd0 1
      · exact hd0 2
      · exact hd0 0
    · intro j; fin_cases j
      · exact hde 1
      · exact hde 2
      · exact hde 0
  · rw [sumDensity_rotate]
    apply third_max_lower ![d 2,d 0,d 1] _ _ (by simpa using hi) he0 he1
    · intro j; fin_cases j
      · exact hd0 2
      · exact hd0 0
      · exact hd0 1
    · intro j; fin_cases j
      · exact hde 2
      · exact hde 0
      · exact hde 1
  · exact third_max_lower d hd0 hde hi he0 he1

theorem logSize_corner_bound {e:ℝ} (he0:0<e) (he1:e≤(1:ℝ)/256) :
    logSize e≤2*Real.log (1/e) := by
  have hehalf : e≤(1:ℝ)/2 := by linarith
  have hlog : 1≤Real.log (1/e) := by
    have h := Real.log_le_log (by norm_num:(0:ℝ)<4)
      ((le_div_iff₀ he0).mpr (by linarith:4*e≤1))
    have h2 : (1:ℝ)/2≤Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num:(0:ℝ)<2)
      norm_num at hh
      linarith
    have hh : Real.log (4:ℝ)=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    linarith
  rw [logSize_eq he0 (by linarith),one_div,Real.log_inv] at *
  linarith

def lowerConstant : ℝ := Real.log 2/4608
def upperConstant : ℝ := 1+4*upperCoefficient.toReal

theorem lowerConstant_pos : 0<lowerConstant := by
  unfold lowerConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
theorem upperConstant_pos : 0<upperConstant := by
  unfold upperConstant
  positivity

/-- Quantitative sharp scale for the literal full sum density, with
fixed numerical constants and no lower bound on the smaller deficits. -/
theorem sumDensity_zero_two_sided (d:Fin 3→ℝ) {e:ℝ}
    (hd0:∀i,0≤d i) (hde:∀i,d i≤e) (hmax:∃i,d i=e)
    (he0:0<e) (he1:e≤(1:ℝ)/256) :
    lowerConstant*e^2*(Real.log (1/e))^2≤(sumDensity d 0).toReal ∧
      (sumDensity d 0).toReal≤upperConstant*e^2*(Real.log (1/e))^2 := by
  have hd1 : ∀i,d i≤1 := fun i=>(hde i).trans (by linarith)
  have hu := sumDensity_zero_upper d hd0 hde hd1 he0
  have htop : upperCoefficient*(ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2<∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top upperCoefficient_finite
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hsum : sumDensity d 0<∞ := hu.trans_lt htop
  have hlog0 : 0≤Real.log (1/e) := Real.log_nonneg ((le_div_iff₀ he0).mpr (by linarith))
  have hhalf : 0≤Real.log (1/e)/2 := by positivity
  have hlog2 : 0≤Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  constructor
  · have hl := ENNReal.toReal_mono hsum.ne (sumDensity_zero_lower d hd0 hde hmax he0 he1)
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hhalf,
      ENNReal.toReal_ofReal hlog2,ENNReal.toReal_ofReal (show 0≤e/48 by positivity),
      ENNReal.toReal_ofNat] at hl
    exact (show lowerConstant*e^2*(Real.log (1/e))^2=
      (Real.log (1/e)/2)^2*(2*Real.log 2)*(e/48)^2 by unfold lowerConstant; ring).le.trans hl
  · have hr := ENNReal.toReal_mono htop.ne hu
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal he0.le,
      ENNReal.toReal_ofReal (logSize_nonneg e)] at hr
    have hL := logSize_corner_bound he0 he1
    have hsq : (logSize e)^2≤4*(Real.log (1/e))^2 := by
      nlinarith [logSize_nonneg e]
    calc
      _ ≤ upperCoefficient.toReal*e^2*(logSize e)^2 := hr
      _ ≤ upperCoefficient.toReal*e^2*(4*(Real.log (1/e))^2) := by
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ upperConstant*e^2*(Real.log (1/e))^2 := by
        unfold upperConstant
        nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg (Real.log (1/e)))]

end
end Resonance.CornerZeroBounds
