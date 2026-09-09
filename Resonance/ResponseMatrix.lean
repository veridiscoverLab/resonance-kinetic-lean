import Resonance.ResponseFiniteAlgebra

/-! Finite matrices obtained from the same constructed full-form inverse. -/
open scoped BigOperators
namespace Resonance.ResponseMatrix
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalVariationalCell CellResponse ResponseFiniteAlgebra

def responseMatrix {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (s : I→Space R→L[ℝ]ℝ) : Matrix I I ℝ :=
  fun i j=>response hR hθ (s i) (s j)

theorem row_readout {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (s : I→Space R→L[ℝ]ℝ)
    (a : I→ℝ) (i : I) :
    (responseMatrix hR hθ s).mulVec a i=s i (solve hR hθ (∑j,a j • s j)) := by
  rw [solve_finite_sum]
  change (∑j,response hR hθ (s i) (s j)*a j)=s i (↑(∑j,a j • solve hR hθ (s j)))
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change s i (solve hR hθ (s j))*a j=a j*s i (solve hR hθ (s j))
  ring

theorem quadratic_readout {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (s : I→Space R→L[ℝ]ℝ) (a : I→ℝ) :
    (∑i,a i*((responseMatrix hR hθ s).mulVec a i))=
      response hR hθ (∑i,a i • s i) (∑i,a i • s i) := by
  rw [response_finite_sum]
  simp only [responseMatrix,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

theorem matrix_kernel_iff {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (s : I→Space R→L[ℝ]ℝ) (a : I→ℝ) :
    (responseMatrix hR hθ s).mulVec a=0 ↔
      response hR hθ (∑i,a i • s i) (∑i,a i • s i)=0 := by
  constructor
  · intro hz
    rw [←quadratic_readout,hz]
    simp
  · intro hz
    rw [response_zero_iff] at hz
    funext i
    rw [row_readout,hz]
    exact map_zero _

theorem response_two_finite_sums {I J : Type*} [Fintype I] [Fintype J]
    {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (s : I→Space R→L[ℝ]ℝ) (t : J→Space R→L[ℝ]ℝ) (a : I→ℝ) (b : J→ℝ) :
    response hR hθ (∑i,a i • s i) (∑j,b j • t j)=
      ∑i,∑j,a i*response hR hθ (s i) (t j)*b j := by
  rw [response,solve_finite_sum]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change a i*(s i) (↑(∑j,b j • solve hR hθ (t j)))=_
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change a i*(b j*(s i) (solve hR hθ (t j)))=a i*(s i) (solve hR hθ (t j))*b j
  ring

end
end Resonance.ResponseMatrix
