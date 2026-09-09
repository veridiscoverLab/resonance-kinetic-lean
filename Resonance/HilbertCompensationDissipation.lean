import Resonance.HilbertCommutatorEstimates
import Resonance.CompensationAbsorption

/-! The full dissipative inequality follows from the constructed rank-two
operator and both original cross terms, uniformly in the frequency and clock. -/
open ContinuousLinearMap InnerProductSpace
namespace Resonance.HilbertCompensationDissipation
noncomputable section
open RankTwoHilbert HilbertQuadraticBounds HilbertCompensatedGenerator
open HilbertCommutatorEstimates FourierCompensationWeights CompensationAbsorption
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem exact_quadratic_identity (A B : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (e v : E) (α r d : ℝ) :
    quadratic (metric (skew (coupling A e) e) α*generator A B r d+
      star (generator A B r d)*metric (skew (coupling A e) e) α) v=
      -2*d*quadratic B v+α*r*quadratic (commutator A e) v+
        α*d*quadratic (-anti (skew (coupling A e) e) B) v := by
  have he : metric (skew (coupling A e) e) α*generator A B r d+
      star (generator A B r d)*metric (skew (coupling A e) e) α=
      ((-2*d:ℝ):ℂ) • B+((α*r:ℝ):ℂ) • commutator A e+
        ((α*d:ℝ):ℂ) • (-anti (skew (coupling A e) e) B) := by
    rw [exact_compensated A B _ hA hB]
    simp only [RankTwoHilbert.commutator,anti,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
    module
  rw [he,quadratic_add,quadratic_add,quadratic_real_smul,quadratic_real_smul,quadratic_real_smul]

theorem compensated_dissipation (A B : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {e : E} (he : ‖e‖=1) (hBe : B e=0) {β k M η c r : ℝ}
    (hβ : 0<β) (hk : k≤‖coupling A e‖^2)
    (hcoerc : ∀v:E,β*‖micro e v‖^2≤quadratic B v)
    (hM1 : ‖commutator A e‖≤M) (hM2 : ‖anti (skew (coupling A e) e) B‖≤M)
    (hη : 0≤η) (hc : 0<c) (hr : 0<r)
    (hsmall1 : 4*M^2*η≤k*β) (hsmall2 : 4*M*η≤β) (v : E) :
    quadratic (metric (skew (coupling A e) e) (alpha η c r)*generator A B r (damping c r)+
      star (generator A B r (damping c r))*metric (skew (coupling A e) e) (alpha η c r)) v≤
      -k*η*rate c r*‖inner ℂ e v‖^2-(β*damping c r/2)*‖micro e v‖^2 := by
  let p := alpha η c r*r
  let q := alpha η c r*damping c r
  have hnon := weight_nonnegative hη hc hr.le
  have hd : 0<damping c r := by unfold damping;positivity
  have hp : 0≤p := mul_nonneg hnon.2.1 hr.le
  have hq : 0≤q := mul_nonneg hnon.2.1 hd.le
  have hM : 0≤M := (norm_nonneg _).trans hM1
  have hpd : p≤η*damping c r := by
    dsimp [p]
    rw [alpha_times_frequency]
    exact mul_le_mul_of_nonneg_left (rate_le_damping hc r) hη
  have hqd : q≤η*damping c r := by
    exact mul_le_mul_of_nonneg_right ((alpha_le_half hη hc r).trans (by linarith)) hd.le
  have hpp : p^2≤η*damping c r*p := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hpd)]
  have hqq : q^2≤η*damping c r*p := cross_weight_square η r hc
  have hsum : p+q≤2*η*damping c r := by linarith
  have hb := hcoerc v
  have hcq := commutator_bound A hA he hk hM1 v
  have haq := negative_anti_bound B hB _ he hBe hM2 v
  have hV : -2*damping c r*quadratic B v+p*quadratic (commutator A e) v+
      q*quadratic (-anti (skew (coupling A e) e) B) v≤
      -2*β*damping c r*‖micro e v‖^2-2*k*p*‖inner ℂ e v‖^2+
      2*M*p*‖inner ℂ e v‖*‖micro e v‖+M*p*‖micro e v‖^2+
      2*M*q*‖inner ℂ e v‖*‖micro e v‖+M*q*‖micro e v‖^2 := by
    have h1 := mul_le_mul_of_nonneg_left hb (show 0≤2*damping c r by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcq hp
    have h3 := mul_le_mul_of_nonneg_left haq hq
    nlinarith
  have hfinal := full_absorption hβ hd hp hM hpp hqq hsum hsmall1 hsmall2 hV
  rw [exact_quadratic_identity A B hA hB]
  convert hfinal using 1
  dsimp [p,q]
  rw [alpha_times_frequency]
  ring

end
end Resonance.HilbertCompensationDissipation
