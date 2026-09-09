import Resonance.SpatialTorusNormalization
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! A genuine Fourier isometry for scalar functions on the original
period-2π spatial torus with probability Haar measure. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.PhysicalScalarFourier
noncomputable section
open SpatialTorusNormalization FreeTransport
abbrev PhysicalScalar := Lp ℂ 2 spatialHaar
abbrev UnitScalar := Lp ℂ 2 unitHaar
abbrev Frequency := Fin 3→ℤ

def toUnit : PhysicalScalar→ₗᵢ[ℂ]UnitScalar :=
  Lp.compMeasurePreservingₗᵢ ℂ coordinates.symm coordinates_inverse_preserving
def toPhysical : UnitScalar→ₗᵢ[ℂ]PhysicalScalar :=
  Lp.compMeasurePreservingₗᵢ ℂ coordinates coordinates_preserving

theorem toUnit_toPhysical (f : UnitScalar) : toUnit (toPhysical f)=f := by
  change Lp.compMeasurePreserving coordinates.symm coordinates_inverse_preserving
    (Lp.compMeasurePreserving coordinates coordinates_preserving f)=f
  rw [←Lp.compMeasurePreserving_comp_apply]
  have hh : coordinates ∘ coordinates.symm=id := funext coordinates.apply_symm_apply
  simp only [hh,Lp.compMeasurePreserving_id_apply]

theorem toPhysical_toUnit (f : PhysicalScalar) : toPhysical (toUnit f)=f := by
  change Lp.compMeasurePreserving coordinates coordinates_preserving
    (Lp.compMeasurePreserving coordinates.symm coordinates_inverse_preserving f)=f
  rw [←Lp.compMeasurePreserving_comp_apply]
  have hh : coordinates.symm ∘ coordinates=id := funext coordinates.symm_apply_apply
  simp only [hh,Lp.compMeasurePreserving_id_apply]

def coordinateIsometry : PhysicalScalar≃ₗᵢ[ℂ]UnitScalar :=
  LinearIsometryEquiv.ofSurjective toUnit (fun f=>⟨toPhysical f,toUnit_toPhysical f⟩)

def fourierIsometry : PhysicalScalar≃ₗᵢ[ℂ]lp (fun _:Frequency=>ℂ) 2 :=
  coordinateIsometry.trans UnitAddTorus.mFourierBasis.repr

def character (n : Frequency) (x : SpatialTorus) : ℂ := UnitAddTorus.mFourier n (coordinates x)

theorem fourier_coefficient (f : PhysicalScalar) (n : Frequency) :
    fourierIsometry f n=∫x,character (-n) x*f x∂spatialHaar := by
  change UnitAddTorus.mFourierBasis.repr (toUnit f) n= _
  rw [UnitAddTorus.mFourierBasis_repr]
  unfold UnitAddTorus.mFourierCoeff
  change (∫y:UnitTorus,UnitAddTorus.mFourier (-n) y • toUnit f y∂unitHaar)= _
  have hc := coordinates_preserving.integral_comp coordinates.toHomeomorph.measurableEmbedding
    (fun y=>UnitAddTorus.mFourier (-n) y • toUnit f y)
  rw [←hc]
  apply integral_congr_ae
  have hf := Lp.coeFn_compMeasurePreserving f coordinates_inverse_preserving
  have hp := coordinates_preserving.quasiMeasurePreserving.ae hf
  filter_upwards [hp] with x hx
  change toUnit f (coordinates x)=f (coordinates.symm (coordinates x)) at hx
  rw [coordinates.symm_apply_apply] at hx
  simp only [hx,character,smul_eq_mul]

theorem physical_parseval (f : PhysicalScalar) :
    HasSum (fun n:Frequency=>‖fourierIsometry f n‖^2) (‖f‖^2) := by
  have h := lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) (fourierIsometry f)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,LinearIsometryEquiv.norm_map] using h

theorem physical_fourier_injective : Function.Injective fourierIsometry :=
  fourierIsometry.injective

end
end Resonance.PhysicalScalarFourier
