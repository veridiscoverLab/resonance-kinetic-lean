import Resonance.ActualSobolevSpace
import Resonance.PhysicalFourierPolynomials

/-! The dense vectors in the completed H^s,M space are realized by
literal trigonometric polynomials on the original physical torus. -/
open MeasureTheory
namespace Resonance.ActualSobolevPolynomials
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualSobolevSpace
open PhysicalScalarFourier PhysicalVectorFourier SpatialTorusNormalization

theorem coefficient_truncation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s)
    (S : Finset Frequency) (n : Frequency) :
    coefficient hR hθ s (truncation s v S) n=
      if n∈S then coefficient hR hθ s v n else 0 := by
  classical
  have hh : truncation s v S n=if n∈S then v n else 0 := by
    simp only [truncation,lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
    simp
  simp only [coefficient,hh]
  split <;> simp_all

theorem original_polynomial_dense {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s) :
    (∀S : Finset Frequency,∀j : Fin 5,
      finitePhysical hR hθ s v S j=ᵐ[spatialHaar]
        (fun x=>∑n∈S,(coefficient hR hθ s v n j)*character n x)) ∧
    (∀S : Finset Frequency,∀n : Frequency,
      vectorFourier (finitePhysical hR hθ s v S) n=
        coefficient hR hθ s (truncation s v S) n) ∧
    Filter.Tendsto (truncation s v) Filter.atTop (nhds v) := by
  refine ⟨?_,?_,finite_fourier_dense s v⟩
  · intro S j
    exact PhysicalFourierPolynomials.finite_polynomial_ae S (coefficient hR hθ s v) j
  · intro S n
    rw [finitePhysical_fourier,coefficient_truncation]

end
end Resonance.ActualSobolevPolynomials
