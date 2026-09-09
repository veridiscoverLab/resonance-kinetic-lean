import Resonance.ResponseMatrix
import Resonance.RankOneGradient

/-! The Fourier symbol is the contraction of the original fifteen-by-fifteen
Onsager tensor, through the same actual full-form inverse. -/
open scoped BigOperators
namespace Resonance.ActualFourierSymbol
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalVariationalCell CellResponse ResponseFiniteAlgebra ResponseMatrix
open ActualOnsagerTensor ActualOnsagerPositive RankOneGradient

def symbolSource {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (ell : Fin 3→ℝ) (a : Fin 5) : Space R→L[ℝ]ℝ := ∑j,ell j • source hR hθ (j,a)

def symbol {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (ell : Fin 3→ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  responseMatrix hR hθ (symbolSource hR hθ ell)

theorem symbol_original_contraction {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (a b : Fin 5) :
    symbol hR hθ ell a b=∑i,∑j,ell i*tensor hR hθ (i,a) (j,b)*ell j := by
  unfold symbol responseMatrix symbolSource
  rw [response_two_finite_sums]
  rfl

theorem symbol_symmetric {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (a b : Fin 5) :
    symbol hR hθ ell a b=symbol hR hθ ell b a :=
  response_symmetric hR hθ _ _

theorem symbol_combined_source {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (e : Fin 5→ℝ) :
    (∑a,e a • symbolSource hR hθ ell a)=∑i,rankOne ell e i • source hR hθ i := by
  simp only [symbolSource,Finset.smul_sum,smul_smul,rankOne,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

theorem symbol_quadratic_identity {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (e : Fin 5→ℝ) :
    (∑a,e a*((symbol hR hθ ell).mulVec e a))=quadraticResponse hR hθ (rankOne ell e) := by
  rw [quadratic_as_response,combined_source]
  change (∑a,e a*((responseMatrix hR hθ (symbolSource hR hθ ell)).mulVec e a))=_
  rw [quadratic_readout,symbol_combined_source]

theorem symbol_positive {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (e : Fin 5→ℝ) :
    0≤∑a,e a*((symbol hR hθ ell).mulVec e a) := by
  rw [symbol_quadratic_identity]
  exact actual_tensor_positive hR hθ _

theorem symbol_kernel_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (e : Fin 5→ℝ) :
    (symbol hR hθ ell).mulVec e=0 ↔ e 1=0 ∧ e 2=0 ∧ e 3=0 ∧ e 4=0 := by
  change (responseMatrix hR hθ (symbolSource hR hθ ell)).mulVec e=0 ↔ _
  rw [matrix_kernel_iff,symbol_combined_source,←combined_source,←quadratic_as_response]
  rw [rankOne_as_gradient,ActualOnsagerNullDirections.actual_null_directions]
  exact rankOne_null_iff hell e

end
end Resonance.ActualFourierSymbol
