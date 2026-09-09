import Resonance.HilbertFlowReality
import Resonance.ActualModeReconstruction

/-! Reality of the original Fourier flow is derived from real matrix
entries and the odd/even frequency parity of J and D. -/
namespace Resonance.ActualFourierReality
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert ActualComplexNormalization
open ActualModeConjugacy ActualModeReconstruction HilbertExponentialFlow HilbertFlowReality

def conjugationLinear : H→ₗ[ℝ]H where
  toFun v:=WithLp.toLp 2 (fun j=>star (v j))
  map_add' v w:=by ext j; simp
  map_smul' a v:=by ext j; simp

set_option backward.isDefEq.respectTransparency false in
def conjugation : H→L[ℝ]H := conjugationLinear.toContinuousLinearMap

theorem conjugation_apply (v : H) (j : Fin 5) : conjugation v j=star (v j) := rfl

theorem conjugation_smul (a : ℂ) (v : H) :
    conjugation (a • v)=star a • conjugation v := by
  ext j
  simp [conjugation_apply]

theorem conjugation_real_operator (M : Matrix (Fin 5) (Fin 5) ℝ) (v : H) :
    conjugation (operator M v)=operator M (conjugation v) := by
  apply WithLp.ofLp_injective 2
  funext j
  change star ((operator M v).ofLp j)=(operator M (conjugation v)).ofLp j
  rw [operator,Matrix.ofLp_toEuclideanCLM,Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec,dotProduct,RealMatrixComplexification.complexify,conjugation_apply]

set_option backward.isDefEq.respectTransparency false in
theorem original_generator_conjugate {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (v : H) :
    conjugation (modeGenerator hR hθ c ell v)=modeGenerator hR hθ c (-ell) (conjugation v) := by
  have ha : A R θ (-ell)=-A R θ ell := by
    have hh := original_A_homogeneous R θ (-1) ell
    rw [neg_one_smul] at hh
    rw [hh]
    apply ContinuousLinearMap.ext
    intro w
    apply WithLp.ofLp_injective 2
    funext j
    change (((-1:ℝ):ℂ))*(A R θ ell w j)= -(A R θ ell w j)
    push_cast
    ring
  have hb : B hR hθ (-ell)=B hR hθ ell := by
    simpa using original_B_homogeneous hR hθ (-1) ell
  simp only [modeGenerator,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    map_sub,conjugation_smul,ha,hb,ContinuousLinearMap.neg_apply]
  rw [A,B,conjugation_real_operator,conjugation_real_operator]
  simp

theorem original_normalized_flow_conjugate {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (v : H)
    {t : ℝ} (ht : 0≤t) :
    conjugation (flow (modeGenerator hR hθ c ell) t v)=
      flow (modeGenerator hR hθ c (-ell)) t (conjugation v) :=
  flow_real_intertwining conjugation _ _ (original_generator_conjugate hR hθ c ell) v ht

theorem physicalFlow_conjugate {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (v : H)
    {t : ℝ} (ht : 0≤t) :
    conjugation (physicalFlow hR hθ c ell t v)=
      physicalFlow hR hθ c (-ell) t (conjugation v) := by
  rw [physicalFlow,inverseOperator,conjugation_real_operator,
    original_normalized_flow_conjugate hR hθ c ell _ ht,
    rootOperator,conjugation_real_operator]
  rfl

end
end Resonance.ActualFourierReality
