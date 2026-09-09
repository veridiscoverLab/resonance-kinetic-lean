import Resonance.PhysicalVectorFourier
import Resonance.PhysicalFourierFrequencies
import Resonance.ActualCoefficientSemigroup

/-! A genuine positive-time semigroup on the original physical 2π torus,
for all five Gram-normalized components together. Its Fourier coefficients
are the original normalized matrix exponentials. -/
open ContinuousLinearMap
open scoped NNReal
namespace Resonance.PhysicalNormalizedSemigroup
noncomputable section
open Thermodynamics MatrixHilbertDictionary PhysicalScalarFourier PhysicalVectorFourier
open PhysicalFourierFrequencies ActualCoefficientSemigroup ActualCompensatedDecay
open HilbertExponentialFlow HilbertCompensatedGenerator FourierCompensationWeights
variable {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
variable {c : ℝ} (hc : 0<c)

def evolution (t : ℝ≥0) : Field→L[ℂ]Field :=
  vectorFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((coefficientSemigroup hR hθ hc radius radius_nonneg direction t).comp
      vectorFourier.toLinearIsometry.toContinuousLinearMap)

theorem evolution_fourier (t : ℝ≥0) (f : Field) :
    vectorFourier (evolution hR hθ hc t f)=
      coefficientSemigroup hR hθ hc radius radius_nonneg direction t (vectorFourier f) :=
  vectorFourier.apply_symm_apply _

theorem evolution_mode (t : ℝ≥0) (f : Field) (n : Frequency) :
    vectorFourier (evolution hR hθ hc t f) n=
      flow (modeGenerator hR hθ (direction n) c (radius n)) t (vectorFourier f n) := by
  rw [evolution_fourier,coefficientSemigroup_apply]

theorem evolution_zero : evolution hR hθ hc 0=1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply vectorFourier.injective
  rw [evolution_fourier,coefficientSemigroup_zero]
  rfl

theorem evolution_add (s t : ℝ≥0) :
    evolution hR hθ hc (s+t)=evolution hR hθ hc s*evolution hR hθ hc t := by
  apply ContinuousLinearMap.ext
  intro f
  apply vectorFourier.injective
  simp only [ContinuousLinearMap.mul_apply]
  rw [evolution_fourier,coefficientSemigroup_add,
    evolution_fourier,evolution_fourier]
  rfl

theorem evolution_norm (t : ℝ≥0) : ‖evolution hR hθ hc t‖≤Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 3)
  intro f
  rw [←vectorFourier.norm_map (evolution hR hθ hc t f),evolution_fourier]
  have hh := (coefficientSemigroup hR hθ hc radius radius_nonneg direction t).le_opNorm (vectorFourier f)
  have hb := mul_le_mul_of_nonneg_right
    (coefficientSemigroup_norm hR hθ hc radius radius_nonneg direction t) (norm_nonneg (vectorFourier f))
  simpa only [vectorFourier.norm_map] using hh.trans hb

theorem evolution_strong_continuous (f : Field) :
    Continuous (fun t : ℝ≥0=>evolution hR hθ hc t f) :=
  vectorFourier.symm.continuous.comp
    (coefficientSemigroup_strong_continuous hR hθ hc radius radius_nonneg direction (vectorFourier f))

theorem evolution_preserves_mean (t : ℝ≥0) (f : Field) :
    vectorFourier (evolution hR hθ hc t f) 0=vectorFourier f 0 := by
  rw [evolution_mode,radius_zero]
  have hg : modeGenerator hR hθ (direction 0) c 0=0 := by
    simp [modeGenerator,generator,damping]
  rw [hg]
  simp [flow,NormedSpace.exp_zero]

end
end Resonance.PhysicalNormalizedSemigroup
