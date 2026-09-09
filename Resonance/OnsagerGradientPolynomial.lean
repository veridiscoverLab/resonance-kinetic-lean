import Resonance.ActualOnsagerKernelBridge
import Resonance.OnsagerPolynomial

/-! Exact coordinate dictionary from the original fifteen transport
drives to their degree-three polynomial, before null-space classification. -/
open scoped BigOperators
namespace Resonance.OnsagerGradientPolynomial
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics
open PhysicalFiveBasis PhysicalProjectionKernel
open ActualOnsagerTensor ActualOnsagerKernelBridge
open CoareaNormalization (euclideanFive)
open QuadraticPointwiseClosure

def gradient (a : Fin 3→ℝ) (B : Fin 3→Fin 3→ℝ) (h : Fin 3→ℝ) : Index→ℝ :=
  fun i=>![a i.1,B i.1 0,B i.1 1,B i.1 2,h i.1] i.2

theorem norm_square_coordinates (k : E) : ‖k‖^2=k 0^2+k 1^2+k 2^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]
  ring

theorem raw_gradient_polynomial (θ : Parameter) (a h : Fin 3→ℝ)
    (B : Fin 3→Fin 3→ℝ) (k : E) :
    rawCombination θ (gradient a B h) k=profile θ k*
      MvPolynomial.eval (fun i=>k i) (OnsagerPolynomial.driving a h B) := by
  simp [rawCombination,gradient,rawDrive,basisFunction,euclideanFive,
    Fintype.sum_prod_type,Fin.sum_univ_succ,norm_square_coordinates,
    OnsagerPolynomial.driving,OnsagerPolynomial.linear,OnsagerPolynomial.quadratic,
    OnsagerPolynomial.radiusSq]
  ring

theorem coefficient_polynomial (b : Coefficients) (k : E) :
    evaluate b k=MvPolynomial.eval (fun i=>k i) (OnsagerPolynomial.invariant b.1 b.2.2
      (fun i=>b.2.1 (ParallelGradientAlgebra.axisPoint 1 i))) := by
  rw [FiveInvariantFinal.evaluate_five_moments,norm_square_coordinates]
  simp [OnsagerPolynomial.invariant,OnsagerPolynomial.linear,OnsagerPolynomial.radiusSq,
    Fin.sum_univ_succ]
  ring

theorem polynomial_coefficient (c e : ℝ) (l : Fin 3→ℝ) (k : E) :
    evaluate (parameterCoefficients ![c,l 0,l 1,l 2,e]) k=
      MvPolynomial.eval (fun i=>k i) (OnsagerPolynomial.invariant c e l) := by
  rw [parameterCoefficients_evaluate]
  simp [Entropy.denominator,euclideanFive,norm_square_coordinates,Fin.sum_univ_succ,
    OnsagerPolynomial.invariant,OnsagerPolynomial.linear,OnsagerPolynomial.radiusSq]
  ring

theorem gradient_exhaustive (ξ : Index→ℝ) :
    gradient (fun j=>ξ (j,0)) (fun j l=>ξ (j,l.castSucc.succ)) (fun j=>ξ (j,4))=ξ := by
  funext i
  rcases i with ⟨j,l⟩
  fin_cases l <;> rfl

end
end Resonance.OnsagerGradientPolynomial
