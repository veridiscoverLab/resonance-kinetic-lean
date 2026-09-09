import Resonance.PhysicalScalarFourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Hermitian symmetry is equivalent to actual real values for physical
scalar L² functions on the original torus, not a freely imposed convention. -/
open MeasureTheory
namespace Resonance.PhysicalFourierReality
noncomputable section
open PhysicalScalarFourier SpatialTorusNormalization

def conjugationLp (f : PhysicalScalar) : PhysicalScalar :=
  Complex.conjCLE.toContinuousLinearMap.compLp f

theorem conjugationLp_ae (f : PhysicalScalar) :
    conjugationLp f=ᵐ[spatialHaar] (fun x=>star (f x)) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp f

theorem character_negative (n : Frequency) (x : FreeTransport.SpatialTorus) :
    character (-n) x=star (character n x) := UnitAddTorus.mFourier_neg

set_option backward.isDefEq.respectTransparency false in
theorem fourier_conjugation (f : PhysicalScalar) (n : Frequency) :
    fourierIsometry (conjugationLp f) n=star (fourierIsometry f (-n)) := by
  rw [fourier_coefficient,fourier_coefficient]
  change (∫x,character (-n) x*conjugationLp f x∂spatialHaar)=
    (starRingEnd ℂ) (∫x,character (- -n) x*f x∂spatialHaar)
  trans ∫x,(starRingEnd ℂ) (character (- -n) x*f x)∂spatialHaar
  · apply integral_congr_ae
    filter_upwards [conjugationLp_ae f] with x hx
    simp only [hx,neg_neg,character_negative,map_mul]
    rfl
  · exact integral_conj

theorem real_iff_fourier_symmetry (f : PhysicalScalar) :
    (∀ᵐx∂spatialHaar,star (f x)=f x) ↔
      ∀n:Frequency,fourierIsometry f (-n)=star (fourierIsometry f n) := by
  constructor
  · intro hf
    have he : conjugationLp f=f := by
      apply Lp.ext
      exact (conjugationLp_ae f).trans hf
    intro n
    have hh := fourier_conjugation f (-n)
    simpa only [he,neg_neg] using hh
  · intro hf
    have he : conjugationLp f=f := by
      apply fourierIsometry.injective
      apply Subtype.ext
      funext n
      rw [fourier_conjugation]
      exact (hf (-n)).symm.trans (by simp)
    have hh := conjugationLp_ae f
    rw [he] at hh
    exact hh.symm

end
end Resonance.PhysicalFourierReality
