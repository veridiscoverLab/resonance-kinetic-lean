import Resonance.CellResponse

/-! The finite response matrix is read from the single constructed
physical inverse, with all mixed coefficients kept. -/
open scoped BigOperators
namespace Resonance.ResponseFiniteAlgebra
noncomputable section
open Set ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalVariationalCell CellResponse

def solverLinear {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    (Space R→L[ℝ]ℝ)→ₗ[ℝ]Micro hR hθ where
  toFun := solve hR hθ
  map_add' := solve_add hR hθ
  map_smul' := solve_smul hR hθ

theorem solve_finite_sum {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (s : I→Space R→L[ℝ]ℝ) (a : I→ℝ) :
    solve hR hθ (∑i,a i • s i)=∑i,a i • solve hR hθ (s i) := by
  change solverLinear hR hθ (∑i,a i • s i)=_
  simp only [map_sum,map_smul]
  rfl

theorem response_finite_sum {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (s : I→Space R→L[ℝ]ℝ) (a b : I→ℝ) :
    response hR hθ (∑i,a i • s i) (∑j,b j • s j)=
      ∑i,∑j,a i*response hR hθ (s i) (s j)*b j := by
  rw [response,solve_finite_sum]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change a i*(s i) (↑(∑j,b j • solve hR hθ (s j)))=_
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change a i*(b j*(s i) (solve hR hθ (s j)))=a i*(s i) (solve hR hθ (s j))*b j
  ring

theorem finite_response_positive {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (s : I→Space R→L[ℝ]ℝ) (a : I→ℝ) :
    0≤∑i,∑j,a i*response hR hθ (s i) (s j)*a j := by
  rw [←response_finite_sum]
  exact response_nonnegative hR hθ _

end
end Resonance.ResponseFiniteAlgebra
