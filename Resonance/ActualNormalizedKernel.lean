import Resonance.ActualMassNormalization

/-! The actual normalized damping has exactly its normalized mass line
as kernel. Normalization retains all four nonmass directions. -/
open Matrix
namespace Resonance.ActualNormalizedKernel
noncomputable section
open Thermodynamics ActualGramRoot ActualGramInverse ActualNormalizedMatrices
open ActualMassNormalization ActualFourierSymbol ActualFourierRank

theorem original_root_inverse_vector {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (v : Parameter) :
    (gramRoot R θ).mulVec (((gramRoot R θ)⁻¹).mulVec v)=v := by
  rw [Matrix.mulVec_mulVec,original_root_mul_inverse hR hθ,Matrix.one_mulVec]

theorem original_normalized_mass_zero {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) :
    (normalizedDamping hR hθ ell).mulVec (massVector R θ)=0 := by
  have hm : (symbol hR hθ ell).mulVec massDirection=0 :=
    (symbol_kernel_iff hR hθ hell massDirection).mpr (by simp [massDirection])
  simp only [normalizedDamping,massVector,←Matrix.mulVec_mulVec,Matrix.mulVec_smul]
  rw [original_inverse_root_vector hR hθ,hm,Matrix.mulVec_zero,smul_zero]

theorem original_normalized_kernel {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (y : Parameter) :
    (normalizedDamping hR hθ ell).mulVec y=0 ↔ ∃a : ℝ,y=a • massVector R θ := by
  constructor
  · intro hz
    have hh := congrArg (fun v=>(gramRoot R θ).mulVec v) hz
    simp only [normalizedDamping,←Matrix.mulVec_mulVec] at hh
    rw [original_root_inverse_vector hR hθ,Matrix.mulVec_zero] at hh
    obtain ⟨a,ha⟩ := (actual_symbol_mass_line hR hθ hell _).mp hh
    have he := congrArg (fun v=>(gramRoot R θ).mulVec v) ha
    change (gramRoot R θ).mulVec (((gramRoot R θ)⁻¹).mulVec y)=
      (gramRoot R θ).mulVec (a • massDirection) at he
    rw [original_root_inverse_vector hR hθ,Matrix.mulVec_smul] at he
    refine ⟨a*massLength R θ,?_⟩
    rw [he,massVector,smul_smul]
    congr 1
    field_simp [(original_mass_length_positive hR hθ).ne']
  · rintro ⟨a,rfl⟩
    rw [Matrix.mulVec_smul,original_normalized_mass_zero hR hθ hell,smul_zero]

theorem original_normalized_damping_positive {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    (normalizedDamping hR hθ ell).PosSemidef := by
  have hs : (symbol hR hθ ell).PosSemidef := .of_dotProduct_mulVec_nonneg
    (original_symbol_symmetric hR hθ ell) (fun v=>by
      simpa [dotProduct] using symbol_positive hR hθ ell v)
  have hh := hs.conjTranspose_mul_mul_same ((gramRoot R θ)⁻¹)
  simpa only [(original_inverse_symmetric hR hθ).eq,normalizedDamping] using hh

end
end Resonance.ActualNormalizedKernel
