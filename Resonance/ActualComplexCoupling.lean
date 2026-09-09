import Resonance.ComplexMatrixInjection
import Resonance.ActualComplexSymbol
import Resonance.ActualEulerCoupling

/-! The original complex Fourier null space contains no nonzero generalized
Euler characteristic, with the actual Gram and flux matrices. -/
namespace Resonance.ActualComplexCoupling
noncomputable section
open Thermodynamics ActualFourierRank ActualEulerCoupling ActualComplexSymbol
open RealMatrixComplexification ComplexMatrixInjection

theorem original_complex_euler_coupling (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) :
    (complexify (spatialMatrix R θ ell)).mulVec (embedVector massDirection)=
      (2 : ℂ) • (complexify (gramMatrix R θ)).mulVec (embedVector (betaDirection ell)) := by
  rw [original_mulVec_embed,original_euler_coupling,original_mulVec_embed]
  funext i
  simp [embedVector,two_smul]
  ring

theorem original_complex_mass_not_characteristic (R : ℝ) (hR : 0<R) (θ : Parameter)
    (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0) (ev : ℂ) :
    (complexify (spatialMatrix R θ ell)).mulVec (embedVector massDirection)≠
      ev • (complexify (gramMatrix R θ)).mulVec (embedVector massDirection) := by
  intro he
  rw [original_complex_euler_coupling,←Matrix.mulVec_smul,←Matrix.mulVec_smul] at he
  have hv := original_injective_complex _ (original_gram_injective R hR θ hθ) he
  apply hell
  funext j
  have hj := congrArg Complex.re (congrFun hv j.castSucc.succ)
  fin_cases j <;> simp [embedVector,betaDirection,massDirection] at hj ⊢ <;> linarith

theorem original_complex_kernel_has_no_characteristic {R : ℝ} (hR : 0<R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) {ell : Fin 3→ℝ} (hell : ell≠0)
    (z : Fin 5→ℂ) (hz : z≠0) (hd : (complexSymbol hR hθ ell).mulVec z=0)
    (ev : ℂ) :
    (complexify (spatialMatrix R θ ell)).mulVec z≠
      ev • (complexify (gramMatrix R θ)).mulVec z := by
  obtain ⟨a,ha⟩ := (original_complex_mass_line hR hθ hell z).mp hd
  have hrepr : z=a • embedVector massDirection := by
    rw [ha]
    congr 1
    funext i
    fin_cases i <;> simp [embedVector,massDirection]
  have hane : a≠0 := by
    intro he
    apply hz
    rw [hrepr,he,zero_smul]
  intro he
  rw [hrepr,Matrix.mulVec_smul,Matrix.mulVec_smul,smul_comm ev a] at he
  have hc : (complexify (spatialMatrix R θ ell)).mulVec (embedVector massDirection)=
      ev • (complexify (gramMatrix R θ)).mulVec (embedVector massDirection) := by
    funext i
    exact mul_left_cancel₀ hane (congrFun he i)
  exact original_complex_mass_not_characteristic R hR θ hθ hell ev hc

end
end Resonance.ActualComplexCoupling
