import Resonance.MatrixHilbertDictionary
import Resonance.ActualGramInverse

/-! The original Gram norm is exactly the Euclidean norm after its true
positive square root; both transformations are actual inverse operators. -/
open Matrix
namespace Resonance.ActualGramHilbert
noncomputable section
open Thermodynamics ActualGramRoot ActualGramInverse MatrixHilbertDictionary
open RealMatrixComplexification ComplexPositiveRoot

def rootOperator (R : ℝ) (θ : Parameter) : H→L[ℂ]H := operator (gramRoot R θ)
def inverseOperator (R : ℝ) (θ : Parameter) : H→L[ℂ]H := operator ((gramRoot R θ)⁻¹)

theorem operator_mul (M N : Matrix (Fin 5) (Fin 5) ℝ) :
    operator (M*N)=operator M*operator N := by
  unfold operator
  rw [complexify_product,map_mul]

theorem operator_one : operator (1 : Matrix (Fin 5) (Fin 5) ℝ)=1 := by
  have he : complexify (1 : Matrix (Fin 5) (Fin 5) ℝ)=1 := by
    ext i j
    by_cases h : i=j <;> simp [complexify,Matrix.one_apply,h]
  rw [operator,he,map_one]

theorem original_root_inverse {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : rootOperator R θ*inverseOperator R θ=1 := by
  rw [rootOperator,inverseOperator,←operator_mul,original_root_mul_inverse hR hθ,operator_one]

theorem original_inverse_root {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : inverseOperator R θ*rootOperator R θ=1 := by
  rw [rootOperator,inverseOperator,←operator_mul,original_inverse_mul_root hR hθ,operator_one]

theorem original_root_square {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : rootOperator R θ*rootOperator R θ=operator (gramMatrix R θ) := by
  rw [rootOperator,←operator_mul,ActualGramRoot.original_root_square hR hθ]

theorem original_root_selfAdjoint {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : IsSelfAdjoint (rootOperator R θ) :=
  operator_selfAdjoint _ (original_root_symmetric hR hθ)

theorem original_gram_norm {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (v : H) :
    ‖rootOperator R θ v‖^2=(inner ℂ v (operator (gramMatrix R θ) v)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hh := (original_root_selfAdjoint hR hθ).isSymmetric v (rootOperator R θ v)
  change inner ℂ (rootOperator R θ v) (rootOperator R θ v)=
    inner ℂ v ((rootOperator R θ*rootOperator R θ) v) at hh
  rw [original_root_square hR hθ] at hh
  exact congrArg Complex.re hh

end
end Resonance.ActualGramHilbert
