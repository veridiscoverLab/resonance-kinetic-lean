import Resonance.RealMatrixComplexification
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! Compatibility of positive real matrix roots with literal
complexification, including the topology needed by the actual Gram root. -/
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Resonance.ComplexPositiveRoot
noncomputable section
open RealMatrixComplexification
local instance : CStarAlgebra (Matrix (Fin 5) (Fin 5) ℂ) where

theorem complexify_hermitian (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : M.IsHermitian) :
    (complexify M).IsHermitian := by
  ext i j
  have hh : M j i=M i j := by simpa using congrFun (congrFun hM.eq i) j
  simp [complexify,Matrix.conjTranspose_apply,hh]

theorem complexify_positive (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : M.PosSemidef) :
    (complexify M).PosSemidef := by
  have hs : ∀i j,M i j=M j i := by
    intro i j
    simpa using congrFun (congrFun hM.isHermitian.eq j) i
  refine .of_dotProduct_mulVec_nonneg (complexify_hermitian M hM.isHermitian) ?_
  intro z
  change 0 ≤ ∑i,conj (z i)*((complexify M).mulVec z i)
  rw [Complex.nonneg_iff,quadratic_re,quadratic_im_zero M hs]
  refine ⟨add_nonneg ?_ ?_,rfl⟩
  · simpa [dotProduct] using hM.dotProduct_mulVec_nonneg (fun i=>(z i).re)
  · simpa [dotProduct] using hM.dotProduct_mulVec_nonneg (fun i=>(z i).im)

theorem complexify_product (M N : Matrix (Fin 5) (Fin 5) ℝ) :
    complexify (M*N)=complexify M*complexify N := by
  ext i j
  simp [complexify,Matrix.mul_apply]

theorem complexify_sqrt (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : M.PosSemidef) :
    CFC.sqrt (complexify M)=complexify (CFC.sqrt M) := by
  apply CFC.sqrt_unique
  · rw [←complexify_product,CFC.sqrt_mul_sqrt_self M hM.nonneg]
  · exact (complexify_positive _ (CFC.sqrt_nonneg M).posSemidef).nonneg

theorem complexify_continuous :
    Continuous (complexify (I := Fin 5)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))

end
end Resonance.ComplexPositiveRoot
