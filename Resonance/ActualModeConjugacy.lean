import Resonance.ActualComplexNormalization
import Resonance.ActualGramHilbert
import Resonance.ActualFrequencyHomogeneity

/-! Exact conjugacy of the original constant five-moment equation and
its Gram-normalized Hilbert evolution. The original time derivative and all
three matrix terms belong to the same mode. -/
namespace Resonance.ActualModeConjugacy
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert ActualComplexNormalization
open ActualGramRoot ActualGramInverse ActualMassNormalization ActualNormalizedMatrices
open ActualEulerCoupling ActualFourierSymbol ActualFrequencyHomogeneity

def realRootOperator (R : ℝ) (θ : Parameter) : H→L[ℝ]H where
  toFun := rootOperator R θ
  map_add' := (rootOperator R θ).map_add
  map_smul' a v := by
    apply WithLp.ofLp_injective 2
    change (RealMatrixComplexification.complexify (gramRoot R θ)).mulVec
        (a • WithLp.ofLp v)=
      a • (RealMatrixComplexification.complexify (gramRoot R θ)).mulVec (WithLp.ofLp v)
    exact Matrix.mulVec_smul _ _ _
  cont := (rootOperator R θ).continuous

def modeGenerator {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) : H→L[ℂ]H :=
  (-Complex.I) • A R θ ell-(c⁻¹ : ℂ) • B hR hθ ell

theorem inverse_gram_operator {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    inverseOperator R θ*operator (gramMatrix R θ)=rootOperator R θ := by
  rw [inverseOperator,←operator_mul,original_inverse_gram hR hθ,rootOperator]

theorem inverse_spatial_operator {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    inverseOperator R θ*operator (spatialMatrix R θ ell)=A R θ ell*rootOperator R θ := by
  rw [inverseOperator,A,rootOperator,←operator_mul,←operator_mul]
  congr 1
  rw [normalizedEuler,Matrix.mul_assoc,original_inverse_mul_root hR hθ,Matrix.mul_one]

theorem inverse_symbol_operator {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    inverseOperator R θ*operator (symbol hR hθ ell)=B hR hθ ell*rootOperator R θ := by
  rw [inverseOperator,B,rootOperator,←operator_mul,←operator_mul]
  congr 1
  rw [normalizedDamping,Matrix.mul_assoc,original_inverse_mul_root hR hθ,Matrix.mul_one]

theorem original_mode_equation {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) (u du : H)
    (hmode : operator (gramMatrix R θ) du+
      Complex.I • operator (spatialMatrix R θ ell) u+
      (c⁻¹ : ℂ) • operator (symbol hR hθ ell) u=0) :
    rootOperator R θ du=modeGenerator hR hθ c ell (rootOperator R θ u) := by
  have hh := congrArg (inverseOperator R θ) hmode
  simp only [map_add,map_smul,map_zero] at hh
  have hm : inverseOperator R θ (operator (gramMatrix R θ) du)=rootOperator R θ du := by
    change (inverseOperator R θ*operator (gramMatrix R θ)) du= _
    rw [inverse_gram_operator hR hθ]
  have hj : inverseOperator R θ (operator (spatialMatrix R θ ell) u)=
      A R θ ell (rootOperator R θ u) := by
    change (inverseOperator R θ*operator (spatialMatrix R θ ell)) u= _
    rw [inverse_spatial_operator hR hθ]
    rfl
  have hd : inverseOperator R θ (operator (symbol hR hθ ell) u)=
      B hR hθ ell (rootOperator R θ u) := by
    change (inverseOperator R θ*operator (symbol hR hθ ell)) u= _
    rw [inverse_symbol_operator hR hθ]
    rfl
  rw [hm,hj,hd,add_assoc] at hh
  have hz := eq_neg_of_add_eq_zero_left hh
  simpa [modeGenerator,neg_add,sub_eq_add_neg,add_comm] using hz

theorem original_mode_derivative {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ)
    {u : ℝ→H} {du : H} {t : ℝ} (hu : HasDerivAt u du t)
    (hmode : operator (gramMatrix R θ) du+
      Complex.I • operator (spatialMatrix R θ ell) (u t)+
      (c⁻¹ : ℂ) • operator (symbol hR hθ ell) (u t)=0) :
    HasDerivAt (fun s=>rootOperator R θ (u s))
      (modeGenerator hR hθ c ell (rootOperator R θ (u t))) t := by
  have hh := (realRootOperator R θ).hasFDerivAt.comp_hasDerivAt t hu
  rw [←original_mode_equation hR hθ c ell (u t) du hmode]
  exact hh

theorem original_A_homogeneous (R : ℝ) (θ : Parameter) (r : ℝ) (ell : Fin 3→ℝ) :
    A R θ (r • ell)=(r : ℂ) • A R θ ell := by
  rw [A,normalized_euler_smul,operator_smul,A]

theorem original_B_homogeneous {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (r : ℝ) (ell : Fin 3→ℝ) :
    B hR hθ (r • ell)=(r^2 : ℂ) • B hR hθ ell := by
  rw [B,normalized_damping_smul,operator_smul,B,Complex.ofReal_pow]

theorem original_mode_derivativeWithin {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ)
    {u : ℝ→H} {du : H} {t : ℝ} {s : Set ℝ} (hu : HasDerivWithinAt u du s t)
    (hmode : operator (gramMatrix R θ) du+
      Complex.I • operator (spatialMatrix R θ ell) (u t)+
      (c⁻¹ : ℂ) • operator (symbol hR hθ ell) (u t)=0) :
    HasDerivWithinAt (fun z=>rootOperator R θ (u z))
      (modeGenerator hR hθ c ell (rootOperator R θ (u t))) s t := by
  have hh := (realRootOperator R θ).hasFDerivAt.comp_hasDerivWithinAt t hu
  rw [←original_mode_equation hR hθ c ell (u t) du hmode]
  exact hh

end
end Resonance.ActualModeConjugacy
