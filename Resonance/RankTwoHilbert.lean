import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! The explicit rank-two compensation on a complex Hilbert space.
The same A and kernel vector e determine every coefficient. -/
open InnerProductSpace ContinuousLinearMap
open scoped ComplexConjugate
namespace Resonance.RankTwoHilbert
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def micro (e : E) : E→L[ℂ]E := ContinuousLinearMap.id ℂ E-rankOne ℂ e e
def coupling (A : E→L[ℂ]E) (e : E) : E := micro e (A e)
def skew (b e : E) : E→L[ℂ]E := rankOne ℂ b e-rankOne ℂ e b
def commutator (A : E→L[ℂ]E) (e : E) : E→L[ℂ]E :=
  skew (coupling A e) e*A-A*skew (coupling A e) e

theorem micro_apply (e v : E) : micro e v=v-inner ℂ e v • e := rfl
theorem skew_apply (b e v : E) :
    skew b e v=inner ℂ e v • b-inner ℂ b v • e := rfl

theorem inner_unit {e : E} (he : ‖e‖=1) : inner ℂ e e=1 := by
  rw [inner_self_eq_norm_sq_to_K,he]
  norm_num

theorem micro_orthogonal {e : E} (he : ‖e‖=1) (v : E) :
    inner ℂ e (micro e v)=0 := by
  rw [micro_apply,inner_sub_right,inner_smul_right,inner_unit he,mul_one,sub_self]

theorem coupling_orthogonal (A : E→L[ℂ]E) {e : E} (he : ‖e‖=1) :
    inner ℂ e (coupling A e)=0 := micro_orthogonal he (A e)

theorem skew_adjoint [CompleteSpace E] (b e : E) : (skew b e).adjoint= -skew b e := by
  simp only [skew,map_sub,adjoint_rankOne]
  abel

theorem skew_unit {b e : E} (he : ‖e‖=1) (hb : inner ℂ e b=0) : skew b e e=b := by
  have hbe : inner ℂ b e=0 := by rw [←inner_conj_symm,hb];simp
  rw [skew_apply,inner_unit he,hbe,one_smul,zero_smul,sub_zero]

theorem skew_unit_pairing {b e : E} (he : ‖e‖=1) (hb : inner ℂ e b=0) (v : E) :
    inner ℂ e (skew b e v)= -inner ℂ b v := by
  rw [skew_apply,inner_sub_right,inner_smul_right,inner_smul_right,hb,inner_unit he]
  simp

theorem coupling_pairing (A : E→L[ℂ]E) {e : E} (he : ‖e‖=1) :
    inner ℂ (coupling A e) (A e)=inner ℂ (coupling A e) (coupling A e) := by
  have hb : inner ℂ (coupling A e) e=0 := by
    rw [←inner_conj_symm,coupling_orthogonal A he];simp
  calc
    _ = inner ℂ (coupling A e) (A e-inner ℂ e (A e) • e) := by
      rw [inner_sub_right,inner_smul_right,hb,mul_zero,sub_zero]
    _ = _ := rfl

theorem exact_commutator_kernel [CompleteSpace E] (A : E→L[ℂ]E) (hA : IsSelfAdjoint A)
    {e : E} (he : ‖e‖=1) :
    inner ℂ e (commutator A e e)= -2*(‖coupling A e‖:ℂ)^2 := by
  have hb := coupling_orthogonal A he
  have hc := coupling_pairing A he
  have hc' : inner ℂ (A e) (coupling A e)=inner ℂ (coupling A e) (coupling A e) := by
    rw [←inner_conj_symm,hc,inner_self_conj]
  have hs : inner ℂ e (A (coupling A e))=inner ℂ (A e) (coupling A e) :=
    (hA.isSymmetric e (coupling A e)).symm
  change inner ℂ e (skew (coupling A e) e (A e)-A (skew (coupling A e) e e))= _
  rw [inner_sub_right,skew_unit he hb,skew_unit_pairing he hb,
    hs,hc,hc',inner_self_eq_norm_sq_to_K]
  ring_nf
  rfl

theorem skew_norm {b e : E} (he : ‖e‖=1) : ‖skew b e‖≤2*‖b‖ := by
  calc
    _ ≤ ‖rankOne ℂ b e‖+‖rankOne ℂ e b‖ := norm_sub_le _ _
    _ = _ := by rw [norm_rankOne,norm_rankOne,he];ring

theorem coupling_norm (A : E→L[ℂ]E) {e : E} (he : ‖e‖=1) :
    ‖coupling A e‖≤2*‖A‖ := by
  have hi := norm_inner_le_norm (𝕜:=ℂ) e (A e)
  have ha := A.le_opNorm e
  rw [he,one_mul] at hi
  rw [he,mul_one] at ha
  calc
    _ ≤ ‖A e‖+‖inner ℂ e (A e) • e‖ := norm_sub_le _ _
    _ = ‖A e‖+‖inner ℂ e (A e)‖ := by rw [norm_smul,he,mul_one]
    _ ≤ 2*‖A‖ := by linarith

theorem norm_decomposition {e : E} (he : ‖e‖=1) (v : E) :
    ‖v‖^2=‖inner ℂ e v‖^2+‖micro e v‖^2 := by
  have ho : inner ℂ (inner ℂ e v • e) (micro e v)=0 := by
    rw [inner_smul_left,micro_orthogonal he v,mul_zero]
  have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  have hv : inner ℂ e v • e+micro e v=v := by rw [micro_apply];abel
  rw [hv,norm_smul,he,mul_one] at hh
  simpa only [pow_two] using hh

end
end Resonance.RankTwoHilbert
