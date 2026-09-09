import Resonance.HilbertCompensationDissipation
import Resonance.CompensationAmplitude

/-! Uniform Hilbert compensation derived from coercivity, coupling, and
operator bounds. The frequency and clock are universally quantified. -/
open ContinuousLinearMap InnerProductSpace
namespace Resonance.UniformHilbertCompensation
noncomputable section
open RankTwoHilbert HilbertQuadraticBounds HilbertCompensatedGenerator
open HilbertCommutatorEstimates FourierCompensationWeights HilbertCompensationDissipation
open CompensationAmplitude
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def energyMetric (A : E→L[ℂ]E) (e : E) (β k L c r : ℝ) : E→L[ℂ]E :=
  metric (skew (coupling A e) e) (alpha (amplitude β k L) c r)
def decayBudget (β k L : ℝ) : ℝ := min (k*amplitude β k L) (β/2)

theorem decayBudget_positive {β k L : ℝ} (hβ : 0<β) (hk : 0<k) (hL : 0≤L) :
    0<decayBudget β k L :=
  lt_min (mul_pos hk (amplitude_bounds hβ hk hL).1) (by positivity)

theorem uniform_compensation (A B : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {e : E} (he : ‖e‖=1) (hBe : B e=0) {β k L : ℝ} (hβ : 0<β) (hk : 0<k)
    (hcoupling : k≤‖coupling A e‖^2)
    (hcoerc : ∀v:E,β*‖micro e v‖^2≤quadratic B v)
    (hAnorm : ‖A‖≤L) (hBnorm : ‖B‖≤L)
    {c r : ℝ} (hc : 0<c) (hr : 0≤r) (v : E) :
    ((1:ℝ)/2)*‖v‖^2≤quadratic (energyMetric A e β k L c r) v ∧
      quadratic (energyMetric A e β k L c r) v≤((3:ℝ)/2)*‖v‖^2 ∧
      quadratic (energyMetric A e β k L c r*generator A B r (damping c r)+
        star (generator A B r (damping c r))*energyMetric A e β k L c r) v≤
          -decayBudget β k L*rate c r*‖v‖^2 := by
  have hL : 0≤L := (norm_nonneg A).trans hAnorm
  let η := amplitude β k L
  have hηs := amplitude_bounds hβ hk hL
  have hη : 0<η := hηs.1
  have hnorm := operator_norm_bounds A B he hAnorm hBnorm
  have hn := weight_nonnegative hη.le hc hr
  have hs : |alpha η c r| * ‖skew (coupling A e) e‖≤1/2 := by
    rw [abs_of_nonneg hn.2.1]
    have ht : alpha η c r*‖skew (coupling A e) e‖≤(η/2)*(4*L) :=
      mul_le_mul (alpha_le_half hη.le hc r) hnorm.1 (norm_nonneg _) (by positivity)
    have hh : η*(4*L)≤1 := hηs.2.2.1
    nlinarith
  have herr := metric_norm_error (skew (coupling A e) e) (alpha η c r) v
  have hcap := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖v‖)
  have haerr : |quadratic (energyMetric A e β k L c r) v-‖v‖^2|≤(1/2)*‖v‖^2 :=
    herr.trans hcap
  refine ⟨by have hh := (abs_le.mp haerr).1;linarith,
    by have hh := (abs_le.mp haerr).2;linarith,?_⟩
  by_cases hr0:r=0
  · subst r
    simp only [generator,damping,rate,zero_pow (by norm_num : (2:ℕ)≠0),zero_div,
      Complex.ofReal_zero,neg_zero,zero_mul,zero_smul,sub_zero,mul_zero,star_zero,
      zero_add,quadratic,ContinuousLinearMap.zero_apply,inner_zero_right,Complex.zero_re]
    rfl
  have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hM1 : ‖commutator A e‖≤crossBudget L := hnorm.2.1.trans (by unfold crossBudget;linarith)
  have hM2 : ‖anti (skew (coupling A e) e) B‖≤crossBudget L :=
    hnorm.2.2.trans (by unfold crossBudget;linarith)
  have hdiss := compensated_dissipation A B hA hB he hBe hβ hcoupling hcoerc hM1 hM2
    hη.le hc hrp hηs.2.2.2.1 hηs.2.2.2.2 v
  have hdel : 0≤decayBudget β k L := (decayBudget_positive hβ hk hL).le
  have hd1 : decayBudget β k L≤k*η := min_le_left _ _
  have hd2 : decayBudget β k L≤β/2 := min_le_right _ _
  have hx := mul_le_mul_of_nonneg_right hd1 (mul_nonneg hn.1 (sq_nonneg ‖inner ℂ e v‖))
  have hy0 : decayBudget β k L*rate c r≤β*damping c r/2 := by
    calc
      _ ≤ (β/2)*rate c r := mul_le_mul_of_nonneg_right hd2 hn.1
      _ ≤ (β/2)*damping c r := mul_le_mul_of_nonneg_left (rate_le_damping hc r) (by positivity)
      _ = _ := by ring
  have hy := mul_le_mul_of_nonneg_right hy0 (sq_nonneg ‖micro e v‖)
  have hsplit := norm_decomposition he v
  change quadratic (metric (skew (coupling A e) e) (alpha η c r)*generator A B r (damping c r)+
    star (generator A B r (damping c r))*metric (skew (coupling A e) e) (alpha η c r)) v≤ _
  rw [hsplit]
  nlinarith

end
end Resonance.UniformHilbertCompensation
