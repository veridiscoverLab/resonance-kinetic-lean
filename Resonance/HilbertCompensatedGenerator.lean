import Resonance.HilbertQuadraticBounds
import Resonance.FourierCompensationWeights

/-! Exact complex Hilbert compensation algebra for the Fourier ODE. -/
open ContinuousLinearMap InnerProductSpace
namespace Resonance.HilbertCompensatedGenerator
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def metric (S : E→L[ℂ]E) (α : ℝ) : E→L[ℂ]E := 1+((α:ℂ)*Complex.I) • S
def generator (A B : E→L[ℂ]E) (r d : ℝ) : E→L[ℂ]E :=
  (-(r:ℂ)*Complex.I) • A-(d:ℂ) • B
def anti (S B : E→L[ℂ]E) : E→L[ℂ]E := Complex.I • (S*B+B*S)

theorem metric_selfAdjoint (S : E→L[ℂ]E) (hS : star S= -S) (α : ℝ) :
    IsSelfAdjoint (metric S α) := by
  change star (metric S α)=metric S α
  simp only [metric,star_add,star_one,star_smul,hS,star_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.conj_I]
  module

theorem generator_star (A B : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (r d : ℝ) : star (generator A B r d)=((r:ℂ)*Complex.I) • A-(d:ℂ) • B := by
  change star A=A at hA
  change star B=B at hB
  simp only [generator,star_sub,star_smul,hA,hB,star_mul,star_neg,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
  module

theorem exact_compensated (A B S : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (α r d : ℝ) :
    metric S α*generator A B r d+star (generator A B r d)*metric S α=
      (-2*(d:ℂ)) • B+((α:ℂ)*r) • (S*A-A*S)-
        ((α:ℂ)*d*Complex.I) • (S*B+B*S) := by
  rw [generator_star A B hA hB]
  simp only [metric,generator,add_mul,mul_add,sub_mul,mul_sub,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

theorem anti_kernel_zero (B : E→L[ℂ]E) (hB : IsSelfAdjoint B)
    (S : E→L[ℂ]E) {e : E} (he : B e=0) : inner ℂ e (anti S B e)=0 := by
  have hs : inner ℂ e (B (S e))=inner ℂ (B e) (S e) := (hB.isSymmetric e (S e)).symm
  change inner ℂ e (Complex.I • (S (B e)+B (S e)))=0
  rw [inner_smul_right,inner_add_right,he,map_zero,inner_zero_right,zero_add,hs,he,inner_zero_left,mul_zero]

omit [CompleteSpace E] in
theorem metric_norm_error (S : E→L[ℂ]E) (α : ℝ) (v : E) :
    |HilbertQuadraticBounds.quadratic (metric S α) v-‖v‖^2|≤|α| * ‖S‖*‖v‖^2 := by
  have he : HilbertQuadraticBounds.quadratic (metric S α) v-‖v‖^2=
      HilbertQuadraticBounds.quadratic (((α:ℂ)*Complex.I) • S) v := by
    have hv : (inner ℂ v v).re=‖v‖^2 := (norm_sq_eq_re_inner (𝕜:=ℂ) v).symm
    simp only [HilbertQuadraticBounds.quadratic,metric,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply,inner_add_right,Complex.add_re,hv]
    ring
  rw [he]
  have hb := HilbertQuadraticBounds.abs_quadratic_bound (((α:ℂ)*Complex.I) • S) v
  simpa only [norm_smul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,mul_assoc] using hb

end
end Resonance.HilbertCompensatedGenerator
