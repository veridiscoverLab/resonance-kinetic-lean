import Resonance.PhysicalScalarFourier

/-! The coordinate normalization preserves the original physical Fourier
characters exp(i n·X). No 2π frequency factor is introduced into the mode
generator by use of the unit-coordinate Fourier library. -/
namespace Resonance.PhysicalFourierCharacters
noncomputable section
open PhysicalScalarFourier SpatialTorusNormalization FreeTransport

theorem character_real (n : Frequency) (X : Fin 3→ℝ) :
    character n (fun j=>(X j:AddCircle period))=
      ∏j:Fin 3,Complex.exp (Complex.I*(n j:ℂ)*(X j:ℂ)) := by
  change (∏j:Fin 3,fourier (n j)
    (coordinates (fun i=>(X i:AddCircle period)) j))= _
  apply Finset.prod_congr rfl
  intro j _
  rw [coordinates_real,fourier_coe_apply]
  congr 1
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.ofReal_div,period,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_one,div_one]
  field_simp

theorem character_continuous (n : Frequency) :
    Continuous (character n) := (UnitAddTorus.mFourier n).continuous.comp coordinates.continuous

end
end Resonance.PhysicalFourierCharacters
