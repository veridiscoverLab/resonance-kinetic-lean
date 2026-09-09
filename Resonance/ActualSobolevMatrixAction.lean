import Resonance.ActualSobolevInclusion

/-! Bounded constant-matrix action in the original Gram Sobolev space.
The same original matrix acts on every decoded physical coefficient. -/
namespace Resonance.ActualSobolevMatrixAction
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert ActualSobolevSpace
open L2DiagonalOperator PhysicalScalarFourier

def action {R : ℝ} (_hR : 0<R) {θ : Parameter} (_hθ : θ∈positiveDomain R)
    (s : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) : Sobolev s→L[ℂ]Sobolev s :=
  diagonal (fun _=>rootOperator R θ*operator M*inverseOperator R θ)
    (norm_nonneg _) (fun _=>le_rfl)

theorem action_coefficient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ)
    (v : Sobolev s) (n : Frequency) :
    coefficient hR hθ s (action hR hθ s M v) n=operator M (coefficient hR hθ s v n) := by
  have hi : ∀w:H,inverseOperator R θ (rootOperator R θ w)=w :=
    fun w=>DFunLike.congr_fun (original_inverse_root hR hθ) w
  change (((weight s n)⁻¹:ℝ):ℂ) • inverseOperator R θ
    (rootOperator R θ (operator M (inverseOperator R θ (v n))))=_
  rw [hi,coefficient,map_smul]

theorem coefficient_add {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v w : Sobolev s) (n : Frequency) :
    coefficient hR hθ s (v+w) n=coefficient hR hθ s v n+coefficient hR hθ s w n := by
  simp only [coefficient,lp.coeFn_add,Pi.add_apply,map_add,smul_add]

theorem coefficient_smul {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (a : ℂ) (v : Sobolev s) (n : Frequency) :
    coefficient hR hθ s (a • v) n=a • coefficient hR hθ s v n := by
  simp only [coefficient,lp.coeFn_smul,Pi.smul_apply,map_smul]
  exact smul_comm _ _ _

theorem coefficient_sum {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) {I : Type*} (S : Finset I)
    (v : I→Sobolev s) (n : Frequency) :
    coefficient hR hθ s (∑i∈S,v i) n=∑i∈S,coefficient hR hθ s (v i) n := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (((weight s n)⁻¹:ℝ):ℂ) • inverseOperator R θ 0=0
    rw [map_zero,smul_zero]
  | @insert i S hi ih => simp only [Finset.sum_insert hi,coefficient_add,ih]

end
end Resonance.ActualSobolevMatrixAction
