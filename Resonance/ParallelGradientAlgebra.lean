import Resonance.ResonantMeasure

/-! The common-gradient consequence of all collision tangent constraints.
Pairwise parallel increments of one field force one scalar affine field;
different pairs are not assigned independent scalar coefficients. -/
open Set

namespace Resonance.ParallelGradientAlgebra
noncomputable section
open ResonantMeasure

def axisPoint (a : ℝ) (j : Fin 3) : E :=
  WithLp.toLp 2 (fun i => if i=j then a else 0)

theorem axisPoint_apply (a : ℝ) (j i : Fin 3) :
    axisPoint a j i = if i=j then a else 0 := rfl

def parallelIncrements (U : Set E) (g : E → E) : Prop :=
  ∀ x∈U, ∀ y∈U, ∀ i j : Fin 3,
    (g x i-g y i)*(x j-y j) = (g x j-g y j)*(x i-y i)

theorem affine_of_parallel_increments (U : Set E) (g : E → E)
    (h0 : (0 : E) ∈ U) (a : ℝ) (ha : a ≠ 0)
    (haxis : ∀ j, axisPoint a j ∈ U) (hg : parallelIncrements U g) :
    ∃ c : ℝ, ∀ x∈U, ∀ i, g x i = g 0 i + c * x i := by
  have hoff (j i : Fin 3) (hij : i ≠ j) : g (axisPoint a j) i = g 0 i := by
    have h := hg (axisPoint a j) (haxis j) 0 h0 i j
    have hm : (g (axisPoint a j) i-g 0 i)*a = 0 := by
      simpa only [axisPoint_apply, PiLp.zero_apply, if_pos rfl, if_neg hij,
        sub_zero, mul_zero] using h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right ha)
  let c : ℝ := (g (axisPoint a 0) 0-g 0 0)/a
  have hc : c*a = g (axisPoint a 0) 0-g 0 0 := by
    dsimp [c]
    rw [div_mul_cancel₀ _ ha]
  have hdiag (j : Fin 3) : g (axisPoint a j) j = g 0 j + c*a := by
    by_cases hj : j=0
    · subst j
      linarith
    · have h := hg (axisPoint a j) (haxis j) (axisPoint a 0) (haxis 0) j 0
      rw [hoff 0 j hj, hoff j 0 (Ne.symm hj)] at h
      simp only [axisPoint_apply, ite_true, if_neg hj, if_neg (Ne.symm hj),
        sub_zero, zero_sub] at h
      have hm : (g (axisPoint a j) j-g 0 j)*a =
          (g (axisPoint a 0) 0-g 0 0)*a := by nlinarith [h]
      have he := mul_right_cancel₀ ha hm
      linarith
  have hseed (j i : Fin 3) : g (axisPoint a j) i = g 0 i + c * axisPoint a j i := by
    by_cases hij : i=j
    · subst i
      simpa only [axisPoint_apply, if_pos rfl] using hdiag j
    · rw [hoff j i hij, axisPoint_apply, if_neg hij]
      ring
  refine ⟨c,?_⟩
  intro x hx i
  obtain ⟨j,hji⟩ := exists_ne i
  have hij : i ≠ j := Ne.symm hji
  have hz := hg x hx 0 h0 i j
  simp only [PiLp.zero_apply, sub_zero] at hz
  have hp := hg x hx (axisPoint a j) (haxis j) i j
  rw [hseed j i, hseed j j] at hp
  simp only [axisPoint_apply, ite_true, if_neg hij, mul_zero, add_zero, sub_zero] at hp
  have hm : (g x i-g 0 i-c*x i)*a=0 := by
    linear_combination hz - hp
  have he := (mul_eq_zero.mp hm).resolve_right ha
  linarith

end
end Resonance.ParallelGradientAlgebra
