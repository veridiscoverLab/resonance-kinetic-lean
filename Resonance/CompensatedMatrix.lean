import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-! Exact compensation algebra for the paper's Fourier generator. The
following finite-dimensional identities are used with the original matrices. -/
open Matrix
open scoped ComplexConjugate
namespace Resonance.CompensatedMatrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

def metric (S : Matrix n n ℂ) (α : ℝ) : Matrix n n ℂ :=
  1+((α : ℂ)*Complex.I) • S

def generator (A B : Matrix n n ℂ) (r d : ℝ) : Matrix n n ℂ :=
  (-(r : ℂ)*Complex.I) • A-(d : ℂ) • B

omit [Fintype n] in
theorem metric_hermitian (S : Matrix n n ℂ) (hS : Sᴴ = -S) (α : ℝ) :
    (metric S α).IsHermitian := by
  change (metric S α)ᴴ=metric S α
  unfold metric
  rw [Matrix.conjTranspose_add,Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul,hS]
  simp only [Complex.star_def,map_mul,Complex.conj_ofReal,Complex.conj_I]
  module

omit [Fintype n] [DecidableEq n] in
theorem generator_adjoint (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (r d : ℝ) :
    (generator A B r d)ᴴ=((r : ℂ)*Complex.I) • A-(d : ℂ) • B := by
  rw [generator,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul,hA.eq,hB.eq]
  simp only [Complex.star_def,map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I]
  module

theorem exact_compensated_matrix (A B S : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (α r d : ℝ) :
    metric S α*generator A B r d+(generator A B r d)ᴴ*metric S α=
      (-2*(d : ℂ)) • B+((α : ℂ)*r) • (S*A-A*S)-
        ((α : ℂ)*d*Complex.I) • (S*B+B*S) := by
  rw [generator_adjoint A B hA hB]
  simp only [metric,generator,add_mul,mul_add,sub_mul,mul_sub,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

end
end Resonance.CompensatedMatrix
