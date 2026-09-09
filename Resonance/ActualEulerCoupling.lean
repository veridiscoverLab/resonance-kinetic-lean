import Resonance.ActualFourierRank
import Resonance.EulerCoefficients

/-! The remaining mass direction is coupled by the original Gram-defined
Euler flux, rather than by an assumed Kawashima condition. -/
open MeasureTheory
open scoped BigOperators
namespace Resonance.ActualEulerCoupling
noncomputable section
open Entropy Thermodynamics EulerCoefficients ActualFourierSymbol ActualFourierRank

def spatialMatrix (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  ∑j,ell j • fluxMatrix R j θ

def betaDirection (ell : Fin 3→ℝ) : Parameter := ![0,ell 0,ell 1,ell 2,0]

theorem original_flux_mass_column (R : ℝ) (θ : Parameter) (j : Fin 3) (i : Fin 5) :
    fluxMatrix R j θ i 0=2*gramMatrix R θ i j.castSucc.succ := by
  rw [fluxMatrix_integral,gramMatrix,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with k
  fin_cases j <;> simp [fiveInvariants] <;> ring

theorem original_euler_coupling (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) :
    (spatialMatrix R θ ell).mulVec massDirection=
      2 • (gramMatrix R θ).mulVec (betaDirection ell) := by
  funext i
  have hm (M : Matrix (Fin 5) (Fin 5) ℝ) : M.mulVec massDirection i=M i 0 := by
    simp [Matrix.mulVec,dotProduct,massDirection,Fin.sum_univ_succ]
  rw [hm]
  simp [spatialMatrix,betaDirection,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    original_flux_mass_column]
  ring

theorem original_gram_injective (R : ℝ) (hR : 0<R) (θ : Parameter)
    (hθ : θ∈positiveDomain R) : Function.Injective (gramMatrix R θ).mulVec := by
  intro a b hab
  by_contra hn
  have hp := gram_quadratic_pos R hR θ hθ (a-b) (sub_ne_zero.mpr hn)
  have hz : (gramMatrix R θ).mulVec (a-b)=0 := by
    rw [Matrix.mulVec_sub,hab,sub_self]
  rw [←gram_quadratic_identity R θ hθ,hz,dotProduct_zero] at hp
  exact (lt_irrefl 0) hp

theorem original_mass_not_characteristic (R : ℝ) (hR : 0<R) (θ : Parameter)
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (ev : ℝ) :
    (spatialMatrix R θ ell).mulVec massDirection≠
      ev • (gramMatrix R θ).mulVec massDirection := by
  intro he
  rw [original_euler_coupling,←Matrix.mulVec_smul,←Matrix.mulVec_smul] at he
  have hv := original_gram_injective R hR θ hθ he
  apply hell
  funext j
  have hj := congrFun hv j.castSucc.succ
  fin_cases j <;> simp [betaDirection,massDirection] at hj ⊢ <;> linarith

end
end Resonance.ActualEulerCoupling
