import Resonance.MarkedPhysicalScaling

/-! Comparing the actual collision frequency of a nested corner box
with that of the original box, at the same physical face deficits. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.SmallBoxFrequency
noncomputable section
open PlaneCoarea CubeAxisCoordinates CornerConvolution CornerZeroBounds CornerLogKernels
open CollisionFrequencyConvolution
set_option maxHeartbeats 1200000

def smallBoxConstant : ℝ := 4*upperCoefficient.toReal/lowerConstant

theorem smallBoxConstant_nonneg : 0 ≤ smallBoxConstant :=
  div_nonneg (by positivity) lowerConstant_pos.le

theorem original_sum_real_upper (d : Fin 3→ℝ) {e : ℝ}
    (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e) (hd1 : ∀i,d i≤1) (he : 0<e) :
    (sumDensity d 0).toReal≤upperCoefficient.toReal*e^2*(logSize e)^2 := by
  have hu := sumDensity_zero_upper d hd0 hde hd1 he
  have ht : upperCoefficient*(ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2<∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top upperCoefficient_finite
    (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hr := ENNReal.toReal_mono ht.ne hu
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal he.le,
    ENNReal.toReal_ofReal (logSize_nonneg e)] using hr

theorem scaled_logSize_bound {e τ : ℝ} (he : 0<e) (hτ : 0<τ)
    (hτ1 : τ≤1) (heτ : e≤τ) : logSize (e/τ)≤logSize e := by
  have hd : 0<e/τ := div_pos he hτ
  have hd1 : e/τ≤1 := (div_le_one hτ).mpr heτ
  rw [logSize_eq hd hd1,logSize_eq he (heτ.trans hτ1)]
  have hle : e≤e/τ := (le_div_iff₀ hτ).mpr (mul_le_of_le_one_right he.le hτ1)
  linarith [Real.log_le_log he hle]

theorem original_scaled_sum_comparison {d : Fin 3→ℝ} {e τ : ℝ}
    (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e) (hmax : ∃i,d i=e)
    (he : 0<e) (he1 : e≤(1:ℝ)/256) (hτ : 0<τ) (hτ1 : τ≤1) (heτ : e≤τ) :
    τ^4*(sumDensity (fun i=>d i/τ) 0).toReal≤
      smallBoxConstant*τ^2*(sumDensity d 0).toReal := by
  have hsmall := original_sum_real_upper (fun i=>d i/τ)
    (fun i=>div_nonneg (hd0 i) hτ.le)
    (fun i=>div_le_div_of_nonneg_right (hde i) hτ.le)
    (fun i=>(div_le_one hτ).mpr ((hde i).trans heτ)) (div_pos he hτ)
  have hlog := scaled_logSize_bound he hτ hτ1 heτ
  have hs : (logSize (e/τ))^2≤(logSize e)^2 := by
    nlinarith [logSize_nonneg (e/τ),logSize_nonneg e]
  have hlog2 := logSize_corner_bound he he1
  have hs2 : (logSize e)^2≤4*(Real.log (1/e))^2 := by nlinarith [logSize_nonneg e]
  have hl := (sumDensity_zero_two_sided d hd0 hde hmax he he1).1
  calc
    _ ≤ τ^4*(upperCoefficient.toReal*(e/τ)^2*(logSize (e/τ))^2) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ ≤ τ^4*(upperCoefficient.toReal*(e/τ)^2*(logSize e)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
    _ = upperCoefficient.toReal*τ^2*e^2*(logSize e)^2 := by field_simp
    _ ≤ upperCoefficient.toReal*τ^2*e^2*(4*(Real.log (1/e))^2) :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ = smallBoxConstant*τ^2*(lowerConstant*e^2*(Real.log (1/e))^2) := by
      unfold smallBoxConstant
      field_simp [lowerConstant_pos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg smallBoxConstant_nonneg (sq_nonneg τ))

theorem actual_small_box_frequency {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ} {e τ : ℝ}
    (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e) (hmax : ∃i,d i=e)
    (he : 0<e) (he1 : e≤(1:ℝ)/256) (hτ : 0<τ) (hτ1 : τ≤1) (heτ : e<τ) :
    CollisionFrequency.geometricFrequency ((L*τ)/2) ((L*τ)•normalizedOutput (fun i=>d i/τ))≤
      smallBoxConstant*τ^2*CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) := by
  have hm := congrArg ENNReal.toReal (original_frequency_eq_convolution (mul_pos hL hτ)
    (fun i=>div_nonneg (hd0 i) hτ.le)
    (fun i=>(div_lt_one hτ).mpr (lt_of_le_of_lt (hde i) heτ)))
  have hn := congrArg ENNReal.toReal (original_frequency_eq_convolution hL hd0
    (fun i=>lt_of_le_of_lt (hde i) (by linarith)))
  simp only [ENNReal.toReal_ofReal (CollisionFrequency.geometricFrequency_nonnegative _ _),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤(L*τ)^4/2)] at hm
  simp only [ENNReal.toReal_ofReal (CollisionFrequency.geometricFrequency_nonnegative _ _),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤L^4/2)] at hn
  rw [hm,hn]
  have h := mul_le_mul_of_nonneg_left
    (original_scaled_sum_comparison hd0 hde hmax he he1 hτ hτ1 heτ.le) (by positivity : 0≤L^4/2)
  convert h using 1 <;> ring

end
end Resonance.SmallBoxFrequency
