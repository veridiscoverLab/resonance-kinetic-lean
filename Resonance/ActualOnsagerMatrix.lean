import Resonance.ActualOnsagerPositive

/-! The matrix kernel is the kernel of the actual combined response,
not just a polynomial null condition imposed on a surrogate matrix. -/
open scoped BigOperators
namespace Resonance.ActualOnsagerMatrix
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalVariationalCell CellResponse ResponseFiniteAlgebra
open ActualOnsagerTensor ActualOnsagerPositive

theorem tensor_row_readout {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) (i : Index) :
    (tensor hR hθ).mulVec a i=source hR hθ i (solve hR hθ (∑j,a j • source hR hθ j)) := by
  rw [solve_finite_sum]
  change (∑j,tensor hR hθ i j*a j)=source hR hθ i (↑(∑j,a j • solve hR hθ (source hR hθ j)))
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change source hR hθ i (solve hR hθ (source hR hθ j))*a j=
    a j*source hR hθ i (solve hR hθ (source hR hθ j))
  ring

theorem quadratic_as_matrix_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    quadraticResponse hR hθ a=∑i,a i*((tensor hR hθ).mulVec a i) := by
  simp only [quadraticResponse,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

theorem actual_matrix_kernel_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    (tensor hR hθ).mulVec a=0 ↔ quadraticResponse hR hθ a=0 := by
  constructor
  · intro hz
    rw [quadratic_as_matrix_pairing,hz]
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  · intro hz
    rw [quadratic_as_response,combined_source,response_zero_iff] at hz
    funext i
    rw [tensor_row_readout,hz]
    exact map_zero _

theorem actual_linear_kernel_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    a∈(Matrix.toLin' (tensor hR hθ)).ker ↔ quadraticResponse hR hθ a=0 :=
  actual_matrix_kernel_iff hR hθ a

end
end Resonance.ActualOnsagerMatrix
