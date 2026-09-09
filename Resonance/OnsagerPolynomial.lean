import Mathlib

/-!
The polynomial part of the Onsager null-space calculation on the original
three-dimensional sharp cube. This file does not identify the polynomial
condition with the kernel of an analytic collision operator.
-/
namespace Resonance.OnsagerPolynomial

open MvPolynomial

abbrev P := MvPolynomial (Fin 3) ℝ

noncomputable def radiusSq : P := X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2

noncomputable def linear (a : Fin 3 → ℝ) : P :=
  C (a 0) * X 0 + C (a 1) * X 1 + C (a 2) * X 2

noncomputable def quadratic (B : Fin 3 → Fin 3 → ℝ) : P :=
  C (B 0 0) * X 0 ^ 2 + C (B 1 1) * X 1 ^ 2 + C (B 2 2) * X 2 ^ 2 +
  C (B 0 1 + B 1 0) * X 0 * X 1 +
  C (B 0 2 + B 2 0) * X 0 * X 2 +
  C (B 1 2 + B 2 1) * X 1 * X 2

noncomputable def driving (a h : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) : P :=
  2 * linear a + 2 * quadratic B + 2 * linear h * radiusSq

noncomputable def invariant (c e : ℝ) (l : Fin 3 → ℝ) : P :=
  C c + linear l + C e * radiusSq

def nullDirections (h : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) : Prop :=
  (∀ i, h i = 0) ∧ B 0 0 = B 1 1 ∧ B 1 1 = B 2 2 ∧
  B 0 1 + B 1 0 = 0 ∧ B 0 2 + B 2 0 = 0 ∧ B 1 2 + B 2 1 = 0

theorem polynomial_null_iff (a h : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) :
    (∃ c e l, driving a h B = invariant c e l) ↔ nullDirections h B := by
  constructor
  · rintro ⟨c, e, l, heq⟩
    have hn20 : (2 : Fin 3) ≠ 0 := by decide
    have hn21 : (2 : Fin 3) ≠ 1 := by decide
    have hz := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then 0 else 0)) heq
    have hx1 := congrArg (eval (fun i : Fin 3 => if i = 0 then 1 else if i = 1 then 0 else 0)) heq
    have hx2 := congrArg (eval (fun i : Fin 3 => if i = 0 then -1 else if i = 1 then 0 else 0)) heq
    have hx3 := congrArg (eval (fun i : Fin 3 => if i = 0 then 2 else if i = 1 then 0 else 0)) heq
    have hy1 := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then 1 else 0)) heq
    have hy2 := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then -1 else 0)) heq
    have hy3 := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then 2 else 0)) heq
    have hz1 := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then 0 else 1)) heq
    have hz2 := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then 0 else -1)) heq
    have hz3 := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then 0 else 2)) heq
    have hxy := congrArg (eval (fun i : Fin 3 => if i = 0 then 1 else if i = 1 then 1 else 0)) heq
    have hxz := congrArg (eval (fun i : Fin 3 => if i = 0 then 1 else if i = 1 then 0 else 1)) heq
    have hyz := congrArg (eval (fun i : Fin 3 => if i = 0 then 0 else if i = 1 then 1 else 1)) heq
    norm_num [driving, invariant, linear, quadratic, radiusSq, Matrix.cons_val, hn20, hn21] at hz hx1 hx2 hx3 hy1 hy2 hy3 hz1 hz2 hz3 hxy hxz hyz
    have hh0 : h 0 = 0 := by linarith only [hz, hx1, hx2, hx3]
    have hh1 : h 1 = 0 := by linarith only [hz, hy1, hy2, hy3]
    have hh2 : h 2 = 0 := by linarith only [hz, hz1, hz2, hz3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hh0
      · exact hh1
      · exact hh2
    all_goals linarith
  · rintro ⟨hh, h00, h11, h01, h02, h12⟩
    refine ⟨0, 2 * B 0 0, fun i => 2 * a i, ?_⟩
    simp [driving, invariant, linear, quadratic, radiusSq, hh, h01, h02, h12,
      ← h00, ← h11, map_mul, map_ofNat]
    ring


open MeasureTheory

/-- The closed cube carries three-dimensional product Lebesgue measure. -/
def cube (R : ℝ) : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-R) R)

def openCube (R : ℝ) : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (-R) R)

/-- A.e. equality on the original cube forces equality of the full polynomials. -/
theorem polynomial_eq_of_cube_ae (R : ℝ) (hR : 0 < R) (p q : P)
    (heq : (fun k => eval k p) =ᵐ[volume.restrict (cube R)] (fun k => eval k q)) :
    p = q := by
  have hsub : openCube R ⊆ cube R := by
    intro k hk i hi
    exact ⟨(hk i hi).1.le, (hk i hi).2.le⟩
  have hopen : IsOpen (openCube R) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hon := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset hsub heq) hopen
    p.continuous_eval.continuousOn q.continuous_eval.continuousOn
  apply MvPolynomial.funext_set (fun _ : Fin 3 => Set.Ioo (-R) R)
    (fun _ => Set.Ioo_infinite (by linarith : -R < R))
  exact hon

/-- Exact polynomial null directions with a.e. sharp-cube quantifiers. -/
theorem cube_null_iff (R : ℝ) (hR : 0 < R)
    (a h : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) :
    (∃ c e l, (fun k => eval k (driving a h B))
      =ᵐ[volume.restrict (cube R)] (fun k => eval k (invariant c e l)))
      ↔ nullDirections h B := by
  constructor
  · rintro ⟨c, e, l, heq⟩
    exact (polynomial_null_iff a h B).mp
      ⟨c, e, l, polynomial_eq_of_cube_ae R hR _ _ heq⟩
  · intro hn
    obtain ⟨c, e, l, heq⟩ := (polynomial_null_iff a h B).mpr hn
    exact ⟨c, e, l, by simp only [heq]; exact Filter.EventuallyEq.rfl⟩


/-- Matrix-language version of the same directions; no analytic operator is assumed. -/
theorem nullDirections_iff_scalar_symmetric (h : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) :
    nullDirections h B ↔
      (∀ i, h i = 0) ∧ ∃ b : ℝ, ∀ i j, B i j + B j i = if i = j then 2*b else 0 := by
  constructor
  · rintro ⟨hh, hd0, hd1, h01, h02, h12⟩
    refine ⟨hh, B 0 0, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
    · ring
    · exact h01
    · exact h02
    · linarith only [h01]
    · linarith only [hd0]
    · exact h12
    · change B 2 0 + B 0 2 = 0
      linarith only [h02]
    · change B 2 1 + B 1 2 = 0
      linarith only [h12]
    · change B 2 2 + B 2 2 = 2 * B 0 0
      linarith only [hd0, hd1]
  · rintro ⟨hh, b, hb⟩
    have hd0 := hb 0 0
    have hd1 := hb 1 1
    have hd2 := hb 2 2
    have h01 := hb 0 1
    have h02 := hb 0 2
    have h12 := hb 1 2
    have hn02 : (0 : Fin 3) ≠ 2 := by decide
    have hn12 : (1 : Fin 3) ≠ 2 := by decide
    norm_num [hn02, hn12] at hd0 hd1 hd2 h01 h02 h12
    refine ⟨hh, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

#print axioms polynomial_null_iff
#print axioms polynomial_eq_of_cube_ae
#print axioms cube_null_iff
#print axioms nullDirections_iff_scalar_symmetric

end Resonance.OnsagerPolynomial
