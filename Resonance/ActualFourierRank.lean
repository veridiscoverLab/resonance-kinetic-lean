import Resonance.ActualFourierSymbol
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact rank four and the original mass-parameter line for every nonzero
spatial frequency. No tensor or rank assertion is assumed. -/
namespace Resonance.ActualFourierRank
noncomputable section
open Thermodynamics ActualFourierSymbol

def massDirection : Fin 5→ℝ := ![1,0,0,0,0]

def restLinear : (Fin 5→ℝ)→ₗ[ℝ](Fin 4→ℝ) where
  toFun := fun e i=>e i.succ
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem rest_zero_iff (e : Fin 5→ℝ) :
    restLinear e=0 ↔ e 1=0 ∧ e 2=0 ∧ e 3=0 ∧ e 4=0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2,congrFun h 3⟩
  · rintro ⟨h1,h2,h3,h4⟩
    funext i
    fin_cases i <;> assumption

theorem rest_surjective : Function.Surjective restLinear := by
  intro e
  refine ⟨![0,e 0,e 1,e 2,e 3],?_⟩
  funext i
  fin_cases i <;> rfl

theorem rest_kernel_dimension : Module.finrank ℝ restLinear.ker=1 := by
  have hh := restLinear.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr rest_surjective] at hh
  have he : Module.finrank ℝ (Fin 5→ℝ)=5 := by simp
  have hr : Module.finrank ℝ (⊤ : Submodule ℝ (Fin 4→ℝ))=4 := by simp
  rw [he,hr] at hh
  omega

theorem actual_symbol_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) :
    (Matrix.toLin' (symbol hR hθ ell)).ker=restLinear.ker := by
  ext e
  exact (symbol_kernel_iff hR hθ hell e).trans (rest_zero_iff e).symm

theorem actual_symbol_kernel_dimension {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) :
    Module.finrank ℝ (Matrix.toLin' (symbol hR hθ ell)).ker=1 := by
  rw [actual_symbol_kernel hR hθ hell]
  exact rest_kernel_dimension

theorem actual_symbol_rank {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) :
    (symbol hR hθ ell).rank=4 := by
  have hh := (Matrix.toLin' (symbol hR hθ ell)).finrank_range_add_finrank_ker
  rw [actual_symbol_kernel_dimension hR hθ hell] at hh
  have he : Module.finrank ℝ (Fin 5→ℝ)=5 := by simp
  rw [he] at hh
  change Module.finrank ℝ (Matrix.toLin' (symbol hR hθ ell)).range=4
  omega

theorem actual_symbol_mass_line {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (e : Fin 5→ℝ) :
    (symbol hR hθ ell).mulVec e=0 ↔ ∃a : ℝ,e=a • massDirection := by
  rw [symbol_kernel_iff hR hθ hell]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨e 0,?_⟩
    funext i
    fin_cases i <;> simp [massDirection,h1,h2,h3,h4]
  · rintro ⟨a,rfl⟩
    simp [massDirection]

end
end Resonance.ActualFourierRank
