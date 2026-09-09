import Resonance.ActualGramRoot

/-! Inversion and energy transport for the original positive Gram root. -/
open Matrix
namespace Resonance.ActualGramInverse
noncomputable section
open Thermodynamics ActualGramRoot RealMatrixComplexification

theorem original_root_mul_inverse {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : gramRoot R θ*(gramRoot R θ)⁻¹=1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (original_root_isUnit hR hθ))

theorem original_inverse_mul_root {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : (gramRoot R θ)⁻¹*gramRoot R θ=1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (original_root_isUnit hR hθ))

theorem original_inverse_symmetric {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ((gramRoot R θ)⁻¹).IsHermitian :=
  (original_root_symmetric hR hθ).inv

theorem original_root_pairing {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v : Parameter) :
    (gramRoot R θ).mulVec u ⬝ᵥ (gramRoot R θ).mulVec v=
      u ⬝ᵥ (gramMatrix R θ).mulVec v := by
  have hs : ∀i j,gramRoot R θ i j=gramRoot R θ j i := by
    intro i j
    simpa using congrFun (congrFun (original_root_symmetric hR hθ).eq j) i
  have hh := real_bilinear_symmetric (gramRoot R θ) hs u ((gramRoot R θ).mulVec v)
  change u ⬝ᵥ (gramRoot R θ).mulVec ((gramRoot R θ).mulVec v)=
    (gramRoot R θ).mulVec v ⬝ᵥ (gramRoot R θ).mulVec u at hh
  rw [Matrix.mulVec_mulVec,original_root_square hR hθ] at hh
  exact (dotProduct_comm _ _).trans hh.symm

theorem original_inverse_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun θ : positiveDomain R=>(gramRoot R θ)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp (original_root_isUnit hR θ.property)
  obtain ⟨u,hu⟩ := hd
  have hi : ContinuousAt Ring.inverse (gramRoot R θ).det :=
    hu ▸ NormedRing.inverse_continuousAt u
  exact ContinuousAt.comp (f := fun θ : positiveDomain R=>gramRoot R θ)
    (g := fun M : Matrix (Fin 5) (Fin 5) ℝ=>M⁻¹) (x := θ)
    (continuousAt_matrix_inv _ hi) (original_root_continuous hR).continuousAt

end
end Resonance.ActualGramInverse
