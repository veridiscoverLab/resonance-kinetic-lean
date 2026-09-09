import Resonance.ActualSpatialDifferentials
import Resonance.ActualSobolevPolynomials

/-! The completed spatial multipliers agree with ordinary derivatives of
the actual finite trigonometric polynomials. Density then fixes the common
Sobolev extension; no alternative notion of spatial derivative is assumed. -/
namespace Resonance.ActualSpatialPolynomials
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualSobolevSpace
open ActualSpatialDifferentials PhysicalFourierDerivatives PhysicalScalarFourier

def polynomial (S : Finset Frequency) (v : Frequency→H) (X : Fin 3→ℝ) : H :=
  ∑n∈S,liftedCharacter n X • v n

def spatialDerivative (f : (Fin 3→ℝ)→H) (j : Fin 3) (X : Fin 3→ℝ) : H :=
  deriv (fun h=>f (axisShift X j h)) 0

set_option backward.isDefEq.respectTransparency false in
theorem polynomial_first (S : Finset Frequency) (v : Frequency→H)
    (j : Fin 3) (X : Fin 3→ℝ) :
    spatialDerivative (polynomial S v) j X=
      polynomial S (fun n=>firstSymbol n j • v n) X := by
  have hd := HasDerivAt.fun_sum (u:=S) (fun n _=>
    (liftedCharacter_axis_hasDerivAt n X j 0).smul_const (v n))
  have he := hd.deriv
  simp only [axisShift_zero] at he
  change deriv (fun h=>∑n∈S,liftedCharacter n (axisShift X j h) • v n) 0=_
  rw [he]
  unfold polynomial firstSymbol
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_smul,mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem polynomial_second (S : Finset Frequency) (v : Frequency→H)
    (i j : Fin 3) (X : Fin 3→ℝ) :
    spatialDerivative (fun Y=>spatialDerivative (polynomial S v) j Y) i X=
      polynomial S (fun n=>secondSymbol n i j • v n) X := by
  simp only [polynomial_first]
  unfold polynomial
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  dsimp only
  rw [smul_smul]
  congr 1
  unfold firstSymbol secondSymbol
  calc
    _=(Complex.I*Complex.I)*((n i:ℂ)*(n j:ℂ)) := by ring
    _=_ := by rw [Complex.I_mul_I]; ring

theorem completed_first_on_polynomial {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (S : Finset Frequency) (v : Sobolev s)
    (j : Fin 3) (X : Fin 3→ℝ) :
    spatialDerivative (polynomial S (coefficient hR hθ s v)) j X=
      polynomial S (coefficient hR hθ (s-2) (first s j v)) X := by
  rw [polynomial_first]
  apply congrArg (fun w=>polynomial S w X)
  funext n
  exact (first_coefficient hR hθ s j v n).symm

theorem completed_second_on_polynomial {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (S : Finset Frequency) (v : Sobolev s)
    (i j : Fin 3) (X : Fin 3→ℝ) :
    spatialDerivative (fun Y=>spatialDerivative (polynomial S (coefficient hR hθ s v)) j Y) i X=
      polynomial S (coefficient hR hθ (s-2) (second s i j v)) X := by
  rw [polynomial_second]
  apply congrArg (fun w=>polynomial S w X)
  funext n
  exact (second_coefficient hR hθ s i j v n).symm

theorem completed_derivatives_are_limits (s : ℝ) (v : Sobolev s) (i j : Fin 3) :
    Filter.Tendsto (fun S=>first s j (truncation s v S)) Filter.atTop (nhds (first s j v)) ∧
      Filter.Tendsto (fun S=>second s i j (truncation s v S)) Filter.atTop (nhds (second s i j v)) :=
  ⟨(first s j).continuous.tendsto v |>.comp (finite_fourier_dense s v),
    (second s i j).continuous.tendsto v |>.comp (finite_fourier_dense s v)⟩

end
end Resonance.ActualSpatialPolynomials
