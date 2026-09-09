import Resonance.HilbertCompensatedGenerator

/-! Bounds for the full commutator and anticommutator; no matrix term is
discarded and the rank-two operator remains determined by A and e. -/
open ContinuousLinearMap InnerProductSpace
namespace Resonance.HilbertCommutatorEstimates
noncomputable section
open RankTwoHilbert HilbertQuadraticBounds HilbertCompensatedGenerator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem operator_norm_bounds (A B : E→L[ℂ]E) {e : E} (he : ‖e‖=1)
    {L : ℝ} (hA : ‖A‖≤L) (hB : ‖B‖≤L) :
    ‖skew (coupling A e) e‖≤4*L ∧
    ‖commutator A e‖≤8*L^2 ∧ ‖anti (skew (coupling A e) e) B‖≤8*L^2 := by
  have hL : 0≤L := (norm_nonneg A).trans hA
  have hS : ‖skew (coupling A e) e‖≤4*L := by
    have hs := skew_norm (b:=coupling A e) he
    have hb := coupling_norm A he
    linarith
  refine ⟨hS,?_,?_⟩
  · calc
      _ ≤ ‖skew (coupling A e) e*A‖+‖A*skew (coupling A e) e‖ := norm_sub_le _ _
      _ ≤ ‖skew (coupling A e) e‖*‖A‖+‖A‖*‖skew (coupling A e) e‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (4*L)*L+L*(4*L) := by gcongr
      _ = _ := by ring
  · calc
      _ = ‖skew (coupling A e) e*B+B*skew (coupling A e) e‖ := by
        rw [anti,norm_smul,Complex.norm_I,one_mul]
      _ ≤ ‖skew (coupling A e) e*B‖+‖B*skew (coupling A e) e‖ := norm_add_le _ _
      _ ≤ ‖skew (coupling A e) e‖*‖B‖+‖B‖*‖skew (coupling A e) e‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (4*L)*L+L*(4*L) := by gcongr
      _ = _ := by ring

omit [CompleteSpace E] in
theorem split_quadratic_bound (T : E→L[ℂ]E) {e : E} (he : ‖e‖=1)
    {k M : ℝ} (hk : quadratic T e≤-2*k) (hM : ‖T‖≤M) (v : E) :
    quadratic T v≤-2*k*‖inner ℂ e v‖^2+
      2*M*‖inner ℂ e v‖*‖micro e v‖+M*‖micro e v‖^2 := by
  have hv : inner ℂ e v • e+micro e v=v := by rw [micro_apply];abel
  have hh := quadratic_sum_bound T he (micro e v) (inner ℂ e v)
  rw [hv] at hh
  have h1 := mul_le_mul_of_nonneg_left hk (sq_nonneg ‖inner ℂ e v‖)
  have h2 := mul_le_mul_of_nonneg_right hM
    (show 0≤2*‖inner ℂ e v‖*‖micro e v‖+‖micro e v‖^2 by positivity)
  nlinarith

theorem commutator_bound (A : E→L[ℂ]E) (hA : IsSelfAdjoint A)
    {e : E} (he : ‖e‖=1) {k M : ℝ} (hk : k≤‖coupling A e‖^2)
    (hM : ‖commutator A e‖≤M) (v : E) :
    quadratic (commutator A e) v≤-2*k*‖inner ℂ e v‖^2+
      2*M*‖inner ℂ e v‖*‖micro e v‖+M*‖micro e v‖^2 := by
  apply split_quadratic_bound _ he _ hM v
  have hq : quadratic (commutator A e) e= -2*‖coupling A e‖^2 := by
    unfold quadratic
    rw [exact_commutator_kernel A hA he]
    norm_num [Complex.mul_re,Complex.mul_im,pow_two]
  rw [hq]
  linarith

theorem negative_anti_bound (B : E→L[ℂ]E) (hB : IsSelfAdjoint B)
    (S : E→L[ℂ]E) {e : E} (he : ‖e‖=1) (hBe : B e=0)
    {M : ℝ} (hM : ‖anti S B‖≤M) (v : E) :
    quadratic (-anti S B) v≤
      2*M*‖inner ℂ e v‖*‖micro e v‖+M*‖micro e v‖^2 := by
  have hq : quadratic (-anti S B) e=0 := by
    rw [quadratic_neg,quadratic,anti_kernel_zero B hB S hBe]
    simp
  have hh := split_quadratic_bound (-anti S B) he (k:=0) (by rw [hq];norm_num)
    (by simpa only [norm_neg] using hM) v
  simpa only [mul_zero,zero_mul,neg_zero,zero_add] using hh

end
end Resonance.HilbertCommutatorEstimates
