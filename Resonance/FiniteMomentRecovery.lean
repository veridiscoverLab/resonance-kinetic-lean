import Resonance.ActualGramCoercivity

/-! Algebra and quantitative inversion for recovery of the original
five kernel coordinates. The actual Gram form and all operator bounds
are supplied by proved concrete definitions in WeightedGramRecovery. -/
namespace Resonance.FiniteMomentRecovery
noncomputable section
open Thermodynamics ActualGramCoercivity

theorem coefficient_bound (G : Parameter→L[ℝ]Parameter) {lam : ℝ} (hlam : 0 < lam)
    (hG : ∀ a,lam*‖a‖^2 ≤ a ⬝ᵥ G a) (a : Parameter) :
    ‖a‖ ≤ (5/lam)*‖G a‖ := by
  by_cases ha : a=0
  · simp [ha]
  · have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hh := (hG a).trans ((le_abs_self _).trans (dotProduct_bound a (G a)))
    have hc : lam*‖a‖ ≤ 5*‖G a‖ := by nlinarith
    rw [div_mul_eq_mul_div,le_div_iff₀ hlam]
    simpa only [mul_comm lam] using hc

section Algebra
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem moving_gram_identity (A : H→L[ℝ]Parameter) (B : H→L[ℝ]H)
    (S : Parameter→L[ℝ]H) (y u g : H) (a : Parameter)
    (hy : y-u=g+S a) (hmatch : A (B y)=0) (hu : A u=0) :
    A (B (S a)) = -A (B g)-A ((B-1) u) := by
  have hh := congrArg (fun v=>A (B v)) hy
  simp only [map_sub,map_add,hmatch,zero_sub] at hh
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,map_sub,hu,sub_zero]
  have h := eq_neg_of_add_eq_zero_left (show A (B g)+A (B (S a))+A (B u)=0 by rw [←hh]; abel)
  calc
    _ = (A (B g)+A (B (S a)))-A (B g) := by abel
    _ = -A (B u)-A (B g) := by rw [h]
    _ = _ := by abel

theorem recovery_bound (A : H→L[ℝ]Parameter) (B : H→L[ℝ]H)
    (S : Parameter→L[ℝ]H) {lam : ℝ} (hlam : 0 < lam)
    (hG : ∀ a,lam*‖a‖^2 ≤ a ⬝ᵥ A (B (S a)))
    (y u g : H) (a : Parameter) (hy : y-u=g+S a)
    (hmatch : A (B y)=0) (hu : A u=0) :
    ‖y-u‖ ≤ ‖g‖+‖S‖*(5/lam)*(‖A‖*‖B‖*‖g‖+‖A‖*‖(B-1) u‖) := by
  let G : Parameter→L[ℝ]Parameter := A.comp (B.comp S)
  have hco := coefficient_bound G hlam hG a
  have hg := moving_gram_identity A B S y u g a hy hmatch hu
  change G a= -A (B g)-A ((B-1) u) at hg
  rw [hg] at hco
  have hn : ‖-A (B g)-A ((B-1) u)‖ ≤ ‖A‖*‖B‖*‖g‖+‖A‖*‖(B-1) u‖ := by
    calc
      _ ≤ ‖A (B g)‖+‖A ((B-1) u)‖ := by simpa only [norm_neg] using norm_sub_le (-A (B g)) (A ((B-1) u))
      _ ≤ ‖A‖*(‖B‖*‖g‖)+‖A‖*‖(B-1) u‖ := by
        gcongr
        · exact (A.le_opNorm (B g)).trans (mul_le_mul_of_nonneg_left (B.le_opNorm g) (norm_nonneg A))
        · exact A.le_opNorm _
      _ = _ := by ring
  rw [hy]
  calc
    _ ≤ ‖g‖+‖S a‖ := norm_add_le _ _
    _ ≤ ‖g‖+‖S‖*‖a‖ := add_le_add le_rfl (S.le_opNorm a)
    _ ≤ ‖g‖+‖S‖*((5/lam)*(‖A‖*‖B‖*‖g‖+‖A‖*‖(B-1) u‖)) := by
      gcongr
      exact hco.trans (mul_le_mul_of_nonneg_left hn (by positivity))
    _ = _ := by ring
end Algebra

end
end Resonance.FiniteMomentRecovery
