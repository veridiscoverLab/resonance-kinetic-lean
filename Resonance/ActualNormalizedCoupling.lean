import Resonance.ActualMassNormalization
import Resonance.RankTwoCompensator

/-! The normalized coupling strength is the original Gram Schur variance. -/
open Matrix
namespace Resonance.ActualNormalizedCoupling
noncomputable section
open Thermodynamics ActualGramRoot ActualGramInverse ActualNormalizedMatrices
open ActualEulerCoupling ActualFourierRank GramCouplingVariance ActualMassNormalization
open RankTwoCompensator

theorem coupling_square {n : Type*} [Fintype n] (A : Matrix n n ℝ) (e : n→ℝ)
    (he : e ⬝ᵥ e=1) :
    coupling A e ⬝ᵥ coupling A e=A.mulVec e ⬝ᵥ A.mulVec e-(e ⬝ᵥ A.mulVec e)^2 := by
  simp only [coupling,sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,he]
  rw [dotProduct_comm (A.mulVec e) e]
  ring

def actualCoupling (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) : Parameter :=
  coupling (normalizedEuler R θ ell) (massVector R θ)

theorem original_coupling_square {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    actualCoupling R θ ell ⬝ᵥ actualCoupling R θ ell=
      4/massSquare R θ*variance R θ ell := by
  rw [actualCoupling,coupling_square _ _ (original_mass_vector_unit hR hθ),
    original_normalized_euler_mass hR hθ]
  simp only [massVector,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    original_root_pairing hR hθ]
  change (2/massLength R θ)*((2/massLength R θ)*quadratic (gramMatrix R θ) (betaDirection ell))-
      ((2/massLength R θ)*((massLength R θ)⁻¹*cross (gramMatrix R θ) massDirection (betaDirection ell)))^2=
    4/massSquare R θ*(quadratic (gramMatrix R θ) (betaDirection ell)-
      cross (gramMatrix R θ) massDirection (betaDirection ell)^2/massSquare R θ)
  rw [←original_mass_length_squared hR hθ]
  field_simp [(original_mass_length_positive hR hθ).ne']
  ring

theorem original_coupling_square_positive {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) :
    0 < actualCoupling R θ ell ⬝ᵥ actualCoupling R θ ell := by
  rw [original_coupling_square hR hθ]
  exact mul_pos (div_pos (by norm_num) (original_mass_square_positive hR hθ))
    (actual_coupling_variance_positive R hR θ hθ hell)

theorem original_coupling_nonzero {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) : actualCoupling R θ ell≠0 := by
  intro he
  have hp := original_coupling_square_positive hR hθ hell
  rw [he,dotProduct_zero] at hp
  exact (lt_irrefl 0) hp

end
end Resonance.ActualNormalizedCoupling
