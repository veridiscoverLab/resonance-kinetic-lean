import Resonance.GramCoefficientContinuity
import Resonance.ComplexPositiveRoot
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! The normalization of the original five-moment Fourier system uses
the positive square root of its actual cube Gram matrix. -/
open Matrix Set
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace Resonance.ActualGramRoot
noncomputable section
open Thermodynamics GramCoefficientContinuity
open ComplexPositiveRoot RealMatrixComplexification
local instance : CStarAlgebra (Matrix (Fin 5) (Fin 5) ℂ) where

def gramRoot (R : ℝ) (θ : Parameter) : Matrix (Fin 5) (Fin 5) ℝ :=
  CFC.sqrt (gramMatrix R θ)

theorem original_root_positive {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : (gramRoot R θ).PosDef :=
  ((gramMatrix_posDef R hR θ hθ).isStrictlyPositive.sqrt).posDef

theorem original_root_square {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : gramRoot R θ*gramRoot R θ=gramMatrix R θ :=
  CFC.sqrt_mul_sqrt_self _ (gramMatrix_posDef R hR θ hθ).posSemidef.nonneg

theorem original_root_symmetric {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : (gramRoot R θ).IsHermitian :=
  (original_root_positive hR hθ).isHermitian

theorem original_root_isUnit {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : IsUnit (gramRoot R θ) :=
  (original_root_positive hR hθ).isUnit

theorem original_root_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun θ : positiveDomain R=>gramRoot R θ) := by
  have hc : Continuous (fun θ : positiveDomain R=>gramMatrix R θ) :=
    continuousOn_iff_continuous_restrict.mp (original_gram_continuousOn R)
  have hm := complexify_continuous.comp hc
  have hh : Continuous (fun θ : positiveDomain R=>CFC.sqrt (complexify (gramMatrix R θ))) :=
    CFC.continuousOn_sqrt.comp_continuous hm
      (fun θ=>(complexify_positive _ (gramMatrix_posDef R hR θ θ.property).posSemidef).nonneg)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have he := Complex.continuous_re.comp
    ((continuous_apply j).comp ((continuous_apply i).comp hh))
  change Continuous (fun θ : positiveDomain R=>
    (CFC.sqrt (complexify (gramMatrix R θ)) i j).re) at he
  have heq : (fun θ : positiveDomain R=>(CFC.sqrt (complexify (gramMatrix R θ)) i j).re)=
      (fun θ : positiveDomain R=>gramRoot R θ i j) := by
    funext θ
    rw [complexify_sqrt _ (gramMatrix_posDef R hR θ θ.property).posSemidef]
    rfl
  rw [heq] at he
  exact he

end
end Resonance.ActualGramRoot
