import Resonance.ActualNormalizedMatrices
import Resonance.GramCouplingVariance

/-! The true mass vector in the Gram-normalized five-moment system. -/
open Matrix
namespace Resonance.ActualMassNormalization
noncomputable section
open Thermodynamics ActualGramRoot ActualGramInverse ActualNormalizedMatrices
open ActualEulerCoupling ActualFourierRank GramCouplingVariance

def massSquare (R : ℝ) (θ : Parameter) : ℝ :=
  quadratic (gramMatrix R θ) massDirection

def massLength (R : ℝ) (θ : Parameter) : ℝ := Real.sqrt (massSquare R θ)

def massVector (R : ℝ) (θ : Parameter) : Parameter :=
  (massLength R θ)⁻¹ • (gramRoot R θ).mulVec massDirection

theorem original_mass_square_positive {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : 0 < massSquare R θ := actual_mass_gram_pos R hR θ hθ

theorem original_mass_length_positive {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : 0 < massLength R θ :=
  Real.sqrt_pos.mpr (original_mass_square_positive hR hθ)

theorem original_mass_length_squared {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : massLength R θ^2=massSquare R θ :=
  Real.sq_sqrt (original_mass_square_positive hR hθ).le

theorem original_mass_vector_unit {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : massVector R θ ⬝ᵥ massVector R θ=1 := by
  have hs := original_mass_length_squared hR hθ
  have hp := original_mass_length_positive hR hθ
  simp only [massVector,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    original_root_pairing hR hθ]
  change (massLength R θ)⁻¹*((massLength R θ)⁻¹*massSquare R θ)=1
  rw [←hs]
  field_simp [hp.ne']

theorem original_inverse_root_vector {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (v : Parameter) :
    ((gramRoot R θ)⁻¹).mulVec ((gramRoot R θ).mulVec v)=v := by
  rw [Matrix.mulVec_mulVec,original_inverse_mul_root hR hθ,Matrix.one_mulVec]

theorem original_inverse_gram {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : (gramRoot R θ)⁻¹*gramMatrix R θ=gramRoot R θ := by
  rw [←original_root_square hR hθ,←Matrix.mul_assoc,original_inverse_mul_root hR hθ,
    Matrix.one_mul]

theorem original_inverse_gram_vector {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (v : Parameter) :
    ((gramRoot R θ)⁻¹).mulVec ((gramMatrix R θ).mulVec v)=(gramRoot R θ).mulVec v := by
  rw [Matrix.mulVec_mulVec,original_inverse_gram hR hθ]

theorem original_normalized_euler_mass {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    (normalizedEuler R θ ell).mulVec (massVector R θ)=
      (2/massLength R θ) • (gramRoot R θ).mulVec (betaDirection ell) := by
  simp only [normalizedEuler,massVector,←Matrix.mulVec_mulVec,Matrix.mulVec_smul]
  rw [original_inverse_root_vector hR hθ,original_euler_coupling]
  simp only [two_smul,Matrix.mulVec_add,original_inverse_gram_vector hR hθ]
  simp only [div_eq_mul_inv]
  module

end
end Resonance.ActualMassNormalization
