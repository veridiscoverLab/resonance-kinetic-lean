import Resonance.ActualEulerCoupling
import Resonance.RealMatrixComplexification

/-! The Euler coupling lower bound is a strictly positive Schur variance
of the same original Gram matrix. -/
open scoped BigOperators
namespace Resonance.GramCouplingVariance
noncomputable section
open Thermodynamics ActualEulerCoupling ActualFourierRank RealMatrixComplexification

def quadratic (M : Matrix (Fin 5) (Fin 5) ℝ) (v : Parameter) : ℝ := v ⬝ᵥ M.mulVec v

def cross (M : Matrix (Fin 5) (Fin 5) ℝ) (v w : Parameter) : ℝ := v ⬝ᵥ M.mulVec w

theorem quadratic_sub_smul (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : ∀i j,M i j=M j i) (a b : Parameter) (t : ℝ) :
    quadratic M (b-t • a)=quadratic M b-2*t*cross M a b+t^2*quadratic M a := by
  have hsym : b ⬝ᵥ M.mulVec a=a ⬝ᵥ M.mulVec b := real_bilinear_symmetric M hs b a
  simp only [quadratic,cross,Matrix.mulVec_sub,Matrix.mulVec_smul,
    sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [hsym]
  ring

theorem actual_mass_gram_pos (R : ℝ) (hR : 0<R) (θ : Parameter)
    (hθ : θ∈positiveDomain R) : 0<quadratic (gramMatrix R θ) massDirection := by
  rw [quadratic,gram_quadratic_identity R θ hθ]
  apply gram_quadratic_pos R hR θ hθ
  intro he
  have h0 := congrFun he 0
  norm_num [massDirection] at h0

def variance (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) : ℝ :=
  quadratic (gramMatrix R θ) (betaDirection ell)-
    (cross (gramMatrix R θ) massDirection (betaDirection ell))^2/
      quadratic (gramMatrix R θ) massDirection

theorem actual_coupling_variance_positive (R : ℝ) (hR : 0<R) (θ : Parameter)
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) : 0<variance R θ ell := by
  let M := gramMatrix R θ
  let m := quadratic M massDirection
  let s := cross M massDirection (betaDirection ell)
  have hm : 0 < m := actual_mass_gram_pos R hR θ hθ
  let v := betaDirection ell-(s/m) • massDirection
  have hv : v≠0 := by
    intro he
    apply hell
    funext j
    have hj := congrFun he j.castSucc.succ
    fin_cases j <;> simpa [v,betaDirection,massDirection] using hj
  have hp : 0<quadratic M v := by
    rw [quadratic,gram_quadratic_identity R θ hθ]
    exact gram_quadratic_pos R hR θ hθ v hv
  have hs : ∀i j,M i j=M j i := by
    intro i j
    exact congrFun (congrFun (gramMatrix_isHermitian R θ) j) i
  have he := quadratic_sub_smul M hs massDirection (betaDirection ell) (s/m)
  have hident : quadratic M v=variance R θ ell := by
    change quadratic M (betaDirection ell-(s/m) • massDirection)=_
    rw [he]
    change quadratic M (betaDirection ell)-2*(s/m)*s+(s/m)^2*m=
      quadratic M (betaDirection ell)-s^2/m
    field_simp [hm.ne']
    ring
  rwa [hident] at hp

end
end Resonance.GramCouplingVariance
