import Resonance.ActualModeConjugacy
import Resonance.HilbertExponentialFlow

/-! Converse conjugacy and the constructed solution of the literal
M du + i J(ell) u + c^-1 D(ell) u = 0 equation. -/
namespace Resonance.ActualModeReconstruction
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert ActualComplexNormalization
open ActualModeConjugacy ActualEulerCoupling ActualFourierSymbol HilbertExponentialFlow

theorem original_equation_of_normalized {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (u du : H)
    (hu : rootOperator R θ du=modeGenerator hR hθ c ell (rootOperator R θ u)) :
    operator (gramMatrix R θ) du+Complex.I • operator (spatialMatrix R θ ell) u+
      (c⁻¹:ℂ) • operator (symbol hR hθ ell) u=0 := by
  let z := operator (gramMatrix R θ) du+Complex.I • operator (spatialMatrix R θ ell) u+
      (c⁻¹:ℂ) • operator (symbol hR hθ ell) u
  have hz : inverseOperator R θ z=0 := by
    dsimp only [z]
    simp only [map_add,map_smul]
    change (inverseOperator R θ*operator (gramMatrix R θ)) du+
      Complex.I • (inverseOperator R θ*operator (spatialMatrix R θ ell)) u+
      (c⁻¹:ℂ) • (inverseOperator R θ*operator (symbol hR hθ ell)) u=0
    rw [inverse_gram_operator hR hθ,inverse_spatial_operator hR hθ,
      inverse_symbol_operator hR hθ]
    simp only [ContinuousLinearMap.mul_apply]
    rw [hu]
    simp [modeGenerator,sub_eq_add_neg,add_assoc]
  have hh := congrArg (rootOperator R θ) hz
  change (rootOperator R θ*inverseOperator R θ) z=rootOperator R θ 0 at hh
  simpa only [original_root_inverse hR hθ,ContinuousLinearMap.one_apply,map_zero] using hh

def realInverseOperator (R : ℝ) (θ : Parameter) : H→L[ℝ]H where
  toFun := inverseOperator R θ
  map_add' := (inverseOperator R θ).map_add
  map_smul' a v := by
    apply WithLp.ofLp_injective 2
    change (RealMatrixComplexification.complexify ((ActualGramRoot.gramRoot R θ)⁻¹)).mulVec
      (a • WithLp.ofLp v)=a •
      (RealMatrixComplexification.complexify ((ActualGramRoot.gramRoot R θ)⁻¹)).mulVec (WithLp.ofLp v)
    exact Matrix.mulVec_smul _ _ _
  cont := (inverseOperator R θ).continuous

def physicalFlow {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (c : ℝ) (ell : Fin 3→ℝ) (t : ℝ) (v : H) : H :=
  inverseOperator R θ (flow (modeGenerator hR hθ c ell) t (rootOperator R θ v))

theorem physicalFlow_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (v : H) :
    physicalFlow hR hθ c ell 0 v=v := by
  have hh := DFunLike.congr_fun (original_inverse_root hR hθ) v
  simpa only [physicalFlow,flow_zero,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.mul_apply] using hh

theorem physicalFlow_hasDerivAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (v : H) (t : ℝ) :
    HasDerivAt (fun s=>physicalFlow hR hθ c ell s v)
      (inverseOperator R θ (modeGenerator hR hθ c ell
        (flow (modeGenerator hR hθ c ell) t (rootOperator R θ v)))) t :=
  (realInverseOperator R θ).hasFDerivAt.comp_hasDerivAt t
    (flow_hasDerivAt (modeGenerator hR hθ c ell) (rootOperator R θ v) t)

theorem physicalFlow_original_equation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (v : H) (t : ℝ) :
    operator (gramMatrix R θ) (inverseOperator R θ (modeGenerator hR hθ c ell
      (flow (modeGenerator hR hθ c ell) t (rootOperator R θ v))))+
      Complex.I • operator (spatialMatrix R θ ell) (physicalFlow hR hθ c ell t v)+
      (c⁻¹:ℂ) • operator (symbol hR hθ ell) (physicalFlow hR hθ c ell t v)=0 := by
  apply original_equation_of_normalized hR hθ c ell
  have hi : ∀w:H,rootOperator R θ (inverseOperator R θ w)=w := by
    intro w
    exact DFunLike.congr_fun (original_root_inverse hR hθ) w
  simp only [physicalFlow,hi]

end
end Resonance.ActualModeReconstruction
