import Resonance.RealMatrixComplexification

/-! The rank-two compensator couples the actual one-dimensional mass
kernel to the other Fourier modes. All identities retain the same A and e. -/
open Matrix
open scoped BigOperators
namespace Resonance.RankTwoCompensator
noncomputable section
variable {n : Type*} [Fintype n]

def coupling (A : Matrix n n ℝ) (e : n→ℝ) : n→ℝ :=
  A.mulVec e-(e ⬝ᵥ A.mulVec e) • e

def skew (b e : n→ℝ) : Matrix n n ℝ := vecMulVec b e-vecMulVec e b

theorem coupling_orthogonal (A : Matrix n n ℝ) (e : n→ℝ) (he : e ⬝ᵥ e=1) :
    e ⬝ᵥ coupling A e=0 := by
  simp [coupling,dotProduct_sub,dotProduct_smul,he]

omit [Fintype n] in
theorem skew_transpose (b e : n→ℝ) : (skew b e).transpose= -(skew b e) := by
  simp [skew,transpose_vecMulVec]

theorem skew_apply (b e v : n→ℝ) :
    (skew b e).mulVec v=(e ⬝ᵥ v) • b-(b ⬝ᵥ v) • e := by
  simp [skew,Matrix.sub_mulVec,vecMulVec_mulVec]

theorem skew_kernel_vector (b e : n→ℝ) (he : e ⬝ᵥ e=1) (hb : e ⬝ᵥ b=0) :
    (skew b e).mulVec e=b := by
  rw [skew_apply,he,dotProduct_comm b e,hb]
  simp

theorem skew_kernel_pairing (b e v : n→ℝ) (he : e ⬝ᵥ e=1) (hb : e ⬝ᵥ b=0) :
    e ⬝ᵥ (skew b e).mulVec v= -(b ⬝ᵥ v) := by
  rw [skew_apply,dotProduct_sub,dotProduct_smul,dotProduct_smul,he,hb]
  simp

theorem coupling_pairing (A : Matrix n n ℝ) (e : n→ℝ) (he : e ⬝ᵥ e=1) :
    coupling A e ⬝ᵥ A.mulVec e=coupling A e ⬝ᵥ coupling A e := by
  have hb := coupling_orthogonal A e he
  have hh : coupling A e ⬝ᵥ e=0 := by rw [dotProduct_comm];exact hb
  conv_rhs => arg 2; rw [coupling]
  rw [dotProduct_sub,dotProduct_smul,hh,smul_zero,sub_zero]

theorem exact_commutator_kernel (A : Matrix n n ℝ) (e : n→ℝ)
    (hA : ∀i j,A i j=A j i) (he : e ⬝ᵥ e=1) :
    e ⬝ᵥ ((skew (coupling A e) e*A-A*skew (coupling A e) e).mulVec e)=
      -2*(coupling A e ⬝ᵥ coupling A e) := by
  have hb := coupling_orthogonal A e he
  rw [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,dotProduct_sub,
    skew_kernel_vector _ _ he hb,skew_kernel_pairing _ _ _ he hb]
  have hs := RealMatrixComplexification.real_bilinear_symmetric A hA e (coupling A e)
  change e ⬝ᵥ A.mulVec (coupling A e)=coupling A e ⬝ᵥ A.mulVec e at hs
  rw [hs,coupling_pairing A e he]
  ring

end
end Resonance.RankTwoCompensator
