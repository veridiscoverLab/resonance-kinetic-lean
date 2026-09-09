import Resonance.HilbertExponentialFlow

/-! The decay estimate for the constructed operator exponential, including
the zero-frequency mode and one common generator for every time. -/
open ContinuousLinearMap InnerProductSpace
namespace Resonance.FourierExponentialDecay
noncomputable section
open RankTwoHilbert HilbertQuadraticBounds HilbertCompensatedGenerator
open FourierCompensationWeights UniformHilbertCompensation FourierODEDecay HilbertExponentialFlow
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
theorem fourier_exponential_decay (A B : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {e : E} (he : ‖e‖=1) (hBe : B e=0) {β k L : ℝ} (hβ : 0<β) (hk : 0<k)
    (hcoupling : k≤‖coupling A e‖^2)
    (hcoerc : ∀v:E,β*‖micro e v‖^2≤quadratic B v)
    (hAnorm : ‖A‖≤L) (hBnorm : ‖B‖≤L)
    {c r : ℝ} (hc : 0<c) (hr : 0≤r) (v : E) {t : ℝ} (ht : 0≤t) :
    ‖flow (generator A B r (damping c r)) t v‖^2≤
      3*Real.exp (-(2*decayBudget β k L/3)*rate c r*t)*‖v‖^2 := by
  have hd := fourier_ODE_decay A B hA hB he hBe hβ hk hcoupling hcoerc hAnorm hBnorm hc hr
    (fun s=>flow_hasDerivAt (generator A B r (damping c r)) v s) ht
  simpa only [flow_zero,ContinuousLinearMap.one_apply] using hd

theorem fourier_exponential_bound (A B : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {e : E} (he : ‖e‖=1) (hBe : B e=0) {β k L : ℝ} (hβ : 0<β) (hk : 0<k)
    (hcoupling : k≤‖coupling A e‖^2)
    (hcoerc : ∀v:E,β*‖micro e v‖^2≤quadratic B v)
    (hAnorm : ‖A‖≤L) (hBnorm : ‖B‖≤L)
    {c r : ℝ} (hc : 0<c) (hr : 0≤r) {t : ℝ} (ht : 0≤t) :
    ‖flow (generator A B r (damping c r)) t‖≤Real.sqrt 3 := by
  have hL : 0≤L := (norm_nonneg A).trans hAnorm
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 3)
  intro v
  have hd := fourier_exponential_decay A B hA hB he hBe hβ hk hcoupling hcoerc hAnorm hBnorm hc hr v ht
  have hrate := (weight_nonnegative (by positivity : (0:ℝ)≤1) hc hr).1
  have he : Real.exp (-(2*decayBudget β k L/3)*rate c r*t)≤1 := by
    apply Real.exp_le_one_iff.mpr
    have hdec := (decayBudget_positive hβ hk hL).le
    have hp : 0≤(2*decayBudget β k L/3)*rate c r*t := by positivity
    nlinarith
  have hs := Real.sq_sqrt (by positivity : (0:ℝ)≤3)
  have hh := mul_le_mul_of_nonneg_right he (show 0≤3*‖v‖^2 by positivity)
  have hs' : (Real.sqrt 3*‖v‖)^2=3*‖v‖^2 := by rw [mul_pow,hs]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))).mp
  rw [hs']
  nlinarith

end
end Resonance.FourierExponentialDecay
