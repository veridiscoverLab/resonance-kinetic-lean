import Resonance.MatrixHilbertDictionary
import Resonance.ActualNormalizedKernel
import Resonance.ActualNormalizedContinuity

/-! The original five-moment matrices in the complex Euclidean space used
by the Fourier evolution. Every coefficient retains its original definition. -/
namespace Resonance.ActualComplexNormalization
noncomputable section
open Thermodynamics ActualNormalizedMatrices ActualNormalizedKernel
open ActualMassNormalization ActualNormalizedCoupling ActualNormalizedContinuity
open MatrixHilbertDictionary ComplexMatrixInjection RealMatrixComplexification

def e (R : ℝ) (θ : Parameter) : H := vector (massVector R θ)
def A (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) : H→L[ℂ]H :=
  operator (normalizedEuler R θ ell)
def B {R : ℝ} (hR : 0 < R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (ell : Fin 3→ℝ) : H→L[ℂ]H := operator (normalizedDamping hR hθ ell)
def b (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) : H :=
  A R θ ell (e R θ)-inner ℂ (e R θ) (A R θ ell (e R θ)) • e R θ

theorem original_e_unit {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ‖e R θ‖=1 := by
  have hn : ‖e R θ‖^2=1 := by
    rw [e,vector_norm_square,original_mass_vector_unit hR hθ]
  nlinarith [norm_nonneg (e R θ)]

theorem original_A_selfAdjoint {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) : IsSelfAdjoint (A R θ ell) :=
  operator_selfAdjoint _ (original_normalized_euler_symmetric hR hθ ell)

theorem original_B_selfAdjoint {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) : IsSelfAdjoint (B hR hθ ell) :=
  operator_selfAdjoint _ (original_normalized_damping_symmetric hR hθ ell)

theorem original_B_mass_zero {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) :
    B hR hθ ell (e R θ)=0 := by
  rw [B,e,operator_vector,original_normalized_mass_zero hR hθ hell]
  rfl

theorem original_b_vector (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) :
    b R θ ell=vector (actualCoupling R θ ell) := by
  simp only [b,A,e,operator_vector,vector_inner,actualCoupling,RankTwoCompensator.coupling]
  apply WithLp.ofLp_injective 2
  change embedVector ((normalizedEuler R θ ell).mulVec (massVector R θ))-
      ((massVector R θ ⬝ᵥ (normalizedEuler R θ ell).mulVec (massVector R θ) : ℝ) : ℂ) •
        embedVector (massVector R θ)=
    embedVector ((normalizedEuler R θ ell).mulVec (massVector R θ)-
      (massVector R θ ⬝ᵥ (normalizedEuler R θ ell).mulVec (massVector R θ)) • massVector R θ)
  rw [←embed_smul]
  funext i
  exact (Complex.ofReal_sub _ _).symm

theorem original_b_square {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    ‖b R θ ell‖^2=4/massSquare R θ*GramCouplingVariance.variance R θ ell := by
  rw [original_b_vector,vector_norm_square,original_coupling_square hR hθ]

theorem original_b_nonzero {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) : b R θ ell≠0 := by
  have hp : 0 < ‖b R θ ell‖^2 := by
    rw [original_b_vector,vector_norm_square]
    exact original_coupling_square_positive hR hθ hell
  intro hz
  simp [hz] at hp

theorem original_B_nonneg {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (v : H) :
    0 ≤ (inner ℂ v (B hR hθ ell v)).re :=
  operator_quadratic_nonneg _ (original_normalized_damping_positive hR hθ ell) v

theorem original_B_zero_iff {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) (v : H) :
    (inner ℂ v (B hR hθ ell v)).re=0 ↔ B hR hθ ell v=0 :=
  operator_quadratic_zero_iff _ (original_normalized_damping_positive hR hθ ell) v

theorem original_complex_kernel {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (v : H) :
    B hR hθ ell v=0 ↔ ∃a : ℂ,v=a • e R θ := by
  constructor
  · intro hz
    have hr : (normalizedDamping hR hθ ell).mulVec (fun i=>(v i).re)=0 := by
      funext i
      have hh := congrArg (fun w : H=>(w i).re) hz
      change ((complexify (normalizedDamping hR hθ ell)).mulVec (WithLp.ofLp v) i).re=0 at hh
      rwa [mulVec_re] at hh
    have hi : (normalizedDamping hR hθ ell).mulVec (fun i=>(v i).im)=0 := by
      funext i
      have hh := congrArg (fun w : H=>(w i).im) hz
      change ((complexify (normalizedDamping hR hθ ell)).mulVec (WithLp.ofLp v) i).im=0 at hh
      rwa [mulVec_im] at hh
    obtain ⟨ar,har⟩ := (original_normalized_kernel hR hθ hell _).mp hr
    obtain ⟨ai,hai⟩ := (original_normalized_kernel hR hθ hell _).mp hi
    refine ⟨⟨ar,ai⟩,?_⟩
    apply WithLp.ofLp_injective 2
    funext i
    apply Complex.ext
    · simpa [e,vector,embedVector] using congrFun har i
    · simpa [e,vector,embedVector] using congrFun hai i
  · rintro ⟨a,rfl⟩
    rw [map_smul,original_B_mass_zero hR hθ hell,smul_zero]

theorem original_e_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun θ : positiveDomain R=>e R θ) :=
  vector_continuous.comp (original_mass_vector_continuous hR)

theorem original_A_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>A R p.1 p.2) :=
  operator_continuous.comp (original_normalized_euler_continuous hR)

theorem original_B_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>B hR p.1.property p.2) :=
  operator_continuous.comp (original_normalized_damping_continuous hR)

theorem original_b_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>b R p.1 p.2) := by
  simp only [original_b_vector]
  exact vector_continuous.comp (original_coupling_continuous hR)

end
end Resonance.ActualComplexNormalization
