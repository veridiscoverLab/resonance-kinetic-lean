import Resonance.ComplexPositiveRoot
import Resonance.ComplexMatrixInjection

/-! Literal real matrices and vectors in the complex Euclidean Hilbert space.
No change of matrix entries or quadratic form occurs in this dictionary. -/
open Matrix
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
namespace Resonance.MatrixHilbertDictionary
noncomputable section
open RealMatrixComplexification ComplexMatrixInjection

abbrev H := EuclideanSpace ℂ (Fin 5)
def vector (v : Fin 5→ℝ) : H := WithLp.toLp 2 (embedVector v)
def operator (A : Matrix (Fin 5) (Fin 5) ℝ) : H→L[ℂ]H :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 5) (complexify A)

theorem operator_vector (A : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5→ℝ) :
    operator A (vector v)=vector (A.mulVec v) := by
  simp only [operator,vector,Matrix.toEuclideanCLM_toLp,original_mulVec_embed]

theorem vector_inner (v w : Fin 5→ℝ) :
    inner ℂ (vector v) (vector w)=((v ⬝ᵥ w : ℝ) : ℂ) := by
  simp [vector,EuclideanSpace.inner_toLp_toLp,dotProduct,embedVector,mul_comm]

theorem vector_norm_square (v : Fin 5→ℝ) :
    ‖vector v‖^2=v ⬝ᵥ v := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),vector_inner]
  rfl

theorem operator_selfAdjoint (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A.IsHermitian) : IsSelfAdjoint (operator A) := by
  change star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 5) (complexify A))=
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 5) (complexify A)
  rw [←map_star]
  exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 5))
    (ComplexPositiveRoot.complexify_hermitian A hA).eq

theorem operator_inner (A : Matrix (Fin 5) (Fin 5) ℝ) (v : H) :
    inner ℂ v (operator A v)=star (WithLp.ofLp v) ⬝ᵥ
      (complexify A).mulVec (WithLp.ofLp v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,operator,Matrix.ofLp_toEuclideanCLM]
  exact dotProduct_comm _ _

theorem operator_quadratic_nonneg (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A.PosSemidef) (v : H) : 0 ≤ (inner ℂ v (operator A v)).re := by
  rw [operator_inner]
  exact (ComplexPositiveRoot.complexify_positive A hA).re_dotProduct_nonneg _

theorem operator_quadratic_zero_iff (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A.PosSemidef) (v : H) :
    (inner ℂ v (operator A v)).re=0 ↔ operator A v=0 := by
  have hp := ComplexPositiveRoot.complexify_positive A hA
  have hn := hp.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  rw [Complex.nonneg_iff] at hn
  rw [operator_inner]
  have he : ((star (WithLp.ofLp v) ⬝ᵥ (complexify A).mulVec (WithLp.ofLp v)).re=0) ↔
      star (WithLp.ofLp v) ⬝ᵥ (complexify A).mulVec (WithLp.ofLp v)=0 := by
    constructor
    · intro hr
      exact Complex.ext hr hn.2.symm
    · intro hz
      exact congrArg Complex.re hz
  rw [he,hp.dotProduct_mulVec_zero_iff]
  constructor
  · intro hz
    apply WithLp.ofLp_injective 2
    simpa only [operator,Matrix.ofLp_toEuclideanCLM,WithLp.ofLp_zero] using hz
  · intro hz
    simpa only [operator,Matrix.ofLp_toEuclideanCLM,WithLp.ofLp_zero] using
      congrArg WithLp.ofLp hz

theorem vector_continuous : Continuous vector := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp (continuous_apply i)

theorem operator_continuous : Continuous operator := by
  exact ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 5)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
    ComplexPositiveRoot.complexify_continuous

end
end Resonance.MatrixHilbertDictionary
