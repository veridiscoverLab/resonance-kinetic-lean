import Resonance.ActualSpatialDifferentials
import Resonance.ActualSobolevDifferentiation
import Resonance.ActualSobolevMatrixAction
import Resonance.ActualSpatialMatrixSymbols

/-! The complete original five-moment linear PDE in H^(s-2), for arbitrary
real s. The time derivative is the actual strong derivative of the same
positive-time semigroup; every original Euler/Onsager spatial slot is kept. -/
namespace Resonance.ActualSobolevPDE
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualSobolevSpace
open ActualSobolevMatrixAction ActualSobolevDifferentiation ActualSpatialDifferentials
open ActualSpatialMatrixSymbols PhysicalScalarFourier
variable {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
variable {c : ℝ} (hc : 0<c)

theorem original_spatial_equation (s : ℝ) (v : Sobolev s) :
    action hR hθ (s-2) (gramMatrix R θ) (differential hR hθ hc s v)+
      ∑j:Fin 3,action hR hθ (s-2) (EulerCoefficients.fluxMatrix R j θ) (first s j v)=
      (c⁻¹:ℂ) • ∑i:Fin 3,∑j:Fin 3,action hR hθ (s-2) (block hR hθ i j) (second s i j v) := by
  apply coefficient_injective hR hθ (s-2)
  funext n
  simp only [coefficient_add,coefficient_sum,coefficient_smul,action_coefficient,
    first_coefficient,second_coefficient,map_smul,firstSymbol,secondSymbol]
  have he := differential_original_equation hR hθ hc s v n
  rw [spatial_operator,diffusion_operator] at he
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,Finset.smul_sum,
    smul_smul] at he
  push_cast at he
  have hd : (∑i:Fin 3,∑j:Fin 3,(-((n i:ℂ)*(n j:ℂ))) •
      operator (block hR hθ i j) (coefficient hR hθ s v n))=
      -(∑i:Fin 3,∑j:Fin 3,((n i:ℂ)*(n j:ℂ)) •
      operator (block hR hθ i j) (coefficient hR hθ s v n)) := by
    simp only [neg_smul,Finset.sum_neg_distrib]
  rw [hd,smul_neg]
  have hsum : (∑i:Fin 3,∑j:Fin 3,((c⁻¹:ℂ)*((n i:ℂ)*(n j:ℂ))) •
      operator (block hR hθ i j) (coefficient hR hθ s v n))=
      (c⁻¹:ℂ) • ∑i:Fin 3,∑j:Fin 3,((n i:ℂ)*(n j:ℂ)) •
      operator (block hR hθ i j) (coefficient hR hθ s v n) := by
    simp only [Finset.smul_sum,smul_smul]
  rw [hsum] at he
  exact eq_neg_of_add_eq_zero_left he

theorem original_evolution_pde (s : ℝ) (v : Sobolev s) {t : ℝ} (ht : 0≤t) :
    HasDerivWithinAt (fun r=>ActualSobolevInclusion.inclusion s (trajectory hR hθ hc s v r))
      (differential hR hθ hc s (trajectory hR hθ hc s v t)) (Set.Ici 0) t ∧
    action hR hθ (s-2) (gramMatrix R θ) (differential hR hθ hc s (trajectory hR hθ hc s v t))+
      ∑j:Fin 3,action hR hθ (s-2) (EulerCoefficients.fluxMatrix R j θ)
        (first s j (trajectory hR hθ hc s v t))=
      (c⁻¹:ℂ) • ∑i:Fin 3,∑j:Fin 3,action hR hθ (s-2) (block hR hθ i j)
        (second s i j (trajectory hR hθ hc s v t)) :=
  ⟨full_sobolev_forward_derivative hR hθ hc s v ht,
    original_spatial_equation hR hθ hc s (trajectory hR hθ hc s v t)⟩

end
end Resonance.ActualSobolevPDE
