import Resonance.RealMatrixComplexification

/-! The original spatial symbol on complex Fourier amplitudes. -/
open scoped BigOperators ComplexConjugate
namespace Resonance.ActualComplexSymbol
noncomputable section
open Thermodynamics ActualFourierSymbol RealMatrixComplexification

def complexSymbol {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (ell : Fin 3→ℝ) : Matrix (Fin 5) (Fin 5) ℂ := complexify (symbol hR hθ ell)

theorem original_complex_quadratic_real {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (z : Fin 5→ℂ) :
    (∑i,conj (z i)*((complexSymbol hR hθ ell).mulVec z i)).im=0 :=
  quadratic_im_zero _ (symbol_symmetric hR hθ ell) z

theorem original_complex_quadratic_nonnegative {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (z : Fin 5→ℂ) :
    0≤(∑i,conj (z i)*((complexSymbol hR hθ ell).mulVec z i)).re := by
  change 0≤(∑i,conj (z i)*((complexify (symbol hR hθ ell)).mulVec z i)).re
  rw [quadratic_re]
  exact add_nonneg (symbol_positive hR hθ ell _) (symbol_positive hR hθ ell _)

theorem original_complex_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (z : Fin 5→ℂ) :
    (complexSymbol hR hθ ell).mulVec z=0 ↔ z 1=0 ∧ z 2=0 ∧ z 3=0 ∧ z 4=0 := by
  change (complexify (symbol hR hθ ell)).mulVec z=0 ↔ _
  rw [complex_kernel_iff,symbol_kernel_iff hR hθ hell,symbol_kernel_iff hR hθ hell]
  constructor
  · rintro ⟨⟨h1,h2,h3,h4⟩,⟨g1,g2,g3,g4⟩⟩
    exact ⟨Complex.ext h1 g1,Complex.ext h2 g2,Complex.ext h3 g3,Complex.ext h4 g4⟩
  · rintro ⟨h1,h2,h3,h4⟩
    simp [h1,h2,h3,h4]

theorem original_complex_mass_line {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (z : Fin 5→ℂ) :
    (complexSymbol hR hθ ell).mulVec z=0 ↔ ∃a : ℂ,z=a • ![1,0,0,0,0] := by
  rw [original_complex_kernel hR hθ hell]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨z 0,?_⟩
    funext i
    fin_cases i <;> simp [h1,h2,h3,h4]
  · rintro ⟨a,rfl⟩
    simp

end
end Resonance.ActualComplexSymbol
