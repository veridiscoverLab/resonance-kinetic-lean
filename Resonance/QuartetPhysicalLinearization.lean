import Mathlib

/-! Pointwise differentiation of the complete quartet product times
the inverse difference. All four source-weight variations cancel by
the same equilibrium identity, before any singular integration. -/
namespace Resonance.QuartetPhysicalLinearization
noncomputable section

def delta (f : Fin 4 → ℝ) : ℝ := f 0+f 1-f 2-f 3
def perturbation (N φ : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ :=
  N i+t*((N i)^2*φ i)
def collisionFactor (N φ : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  (∏ i,perturbation N φ t i)*delta (fun i => (perturbation N φ t i)⁻¹)

theorem perturbation_derivative (N φ : Fin 4 → ℝ) (i : Fin 4) :
    HasDerivAt (fun t => perturbation N φ t i) ((N i)^2*φ i) 0 := by
  simpa only [one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const ((N i)^2*φ i)).const_add (N i)

theorem inverse_derivative (N φ : Fin 4 → ℝ) (hN : ∀ i,N i≠0) (i : Fin 4) :
    HasDerivAt (fun t => (perturbation N φ t i)⁻¹) (-φ i) 0 := by
  have h := (perturbation_derivative N φ i).inv (by simpa [perturbation] using hN i)
  convert h using 1
  simp only [perturbation,zero_mul,add_zero]
  field_simp [hN i]

theorem inverse_delta_derivative (N φ : Fin 4 → ℝ) (hN : ∀ i,N i≠0) :
    HasDerivAt (fun t => delta (fun i => (perturbation N φ t i)⁻¹)) (-delta φ) 0 := by
  have h := (((inverse_derivative N φ hN 0).add (inverse_derivative N φ hN 1)).sub
    (inverse_derivative N φ hN 2)).sub (inverse_derivative N φ hN 3)
  convert h using 1
  simp only [delta]
  ring

theorem complete_equilibrium_linearization (N φ : Fin 4 → ℝ) (hN : ∀ i,N i≠0)
    (heq : delta (fun i => (N i)⁻¹)=0) :
    HasDerivAt (collisionFactor N φ) (-(∏ i,N i)*delta φ) 0 := by
  have hp : DifferentiableAt ℝ (fun t => ∏ i,perturbation N φ t i) 0 := by
    unfold perturbation
    fun_prop
  have h := hp.hasDerivAt.mul (inverse_delta_derivative N φ hN)
  convert h using 1
  simp only [perturbation,zero_mul,add_zero,heq,mul_zero,zero_add]
  ring

theorem weighted_complete_linearization (N φ : Fin 4 → ℝ) (hN : ∀ i,N i≠0)
    (heq : delta (fun i => (N i)⁻¹)=0) (c : ℝ) :
    HasDerivAt (fun t => c*collisionFactor N φ t) (-(c*(∏ i,N i))*delta φ) 0 := by
  convert (complete_equilibrium_linearization N φ hN heq).const_mul c using 1; ring

end
end Resonance.QuartetPhysicalLinearization
