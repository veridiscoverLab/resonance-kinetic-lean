import Resonance.ActualGeneratorOrder
import Resonance.ActualSobolevSemigroup
import Resonance.L2SmoothedEvolution

/-! Strong time differentiation of the original evolution after the actual
H^s to H^(s-2) inclusion. No differentiability in H^s is asserted for arbitrary
H^s data. The resulting derivative satisfies the literal original matrix
equation at every integer Fourier mode of the same source. -/
open Set MeasureTheory
namespace Resonance.ActualSobolevDifferentiation
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert ActualSobolevSpace
open ActualSobolevInclusion ActualGeneratorOrder ActualSobolevSemigroup
open PhysicalFourierFrequencies PhysicalScalarFourier L2DiagonalOperator
open ActualCompensatedDecay ActualModeReconstruction ActualOriginalModeDecay
variable {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
variable {c : ℝ} (hc : 0<c)

def generatorBound : ℝ := (original_generator_order hR hθ hc).choose

theorem generatorBound_nonneg : 0≤generatorBound hR hθ hc :=
  (original_generator_order hR hθ hc).choose_spec.1

theorem generatorBound_spec (n : Frequency) :
    ‖smoothing n*modeGenerator hR hθ (direction n) c (radius n)‖≤generatorBound hR hθ hc :=
  (original_generator_order hR hθ hc).choose_spec.2 n

def differential (s : ℝ) : Sobolev s→L[ℂ]Sobolev (s-2) :=
  diagonal (fun n=>smoothing n*modeGenerator hR hθ (direction n) c (radius n))
    (generatorBound_nonneg hR hθ hc) (generatorBound_spec hR hθ hc)

theorem differential_apply (s : ℝ) (v : Sobolev s) (n : Frequency) :
    differential hR hθ hc s v n=(attenuation n:ℂ) •
      modeGenerator hR hθ (direction n) c (radius n) (v n) := rfl

def trajectory (s : ℝ) (v : Sobolev s) (t : ℝ) : Sobolev s :=
  evolution hR hθ hc s (Real.toNNReal t) v

theorem trajectory_continuous (s : ℝ) (v : Sobolev s) :
    Continuous (trajectory hR hθ hc s v) :=
  (evolution_strong_continuous hR hθ hc s v).comp continuous_real_toNNReal

theorem full_sobolev_integral (s : ℝ) (v : Sobolev s) {t : ℝ} (ht : 0≤t) :
    inclusion s (trajectory hR hθ hc s v t)=inclusion s v+
      ∫r in 0..t,differential hR hθ hc s (trajectory hR hθ hc s v r) :=
  L2SmoothedEvolution.complete_integral_identity
    (fun n=>modeGenerator hR hθ (direction n) c (radius n)) smoothing
    (Real.sqrt_nonneg 3)
    (fun t n=>ActualFourierExponential.original_exponential_bound hR hθ
      (direction n) hc (radius_nonneg n) t.property)
    (by norm_num) smoothing_norm (generatorBound_nonneg hR hθ hc)
    (generatorBound_spec hR hθ hc) v ht

theorem full_sobolev_forward_derivative (s : ℝ) (v : Sobolev s) {t : ℝ} (ht : 0≤t) :
    HasDerivWithinAt (fun r=>inclusion s (trajectory hR hθ hc s v r))
      (differential hR hθ hc s (trajectory hR hθ hc s v t)) (Ici 0) t :=
  L2SmoothedEvolution.complete_forward_derivative
    (fun n=>modeGenerator hR hθ (direction n) c (radius n)) smoothing
    (Real.sqrt_nonneg 3)
    (fun t n=>ActualFourierExponential.original_exponential_bound hR hθ
      (direction n) hc (radius_nonneg n) t.property)
    (by norm_num) smoothing_norm (generatorBound_nonneg hR hθ hc)
    (generatorBound_spec hR hθ hc) v ht

theorem differential_original_equation (s : ℝ) (v : Sobolev s) (n : Frequency) :
    operator (gramMatrix R θ) (coefficient hR hθ (s-2) (differential hR hθ hc s v) n)+
      Complex.I • operator (ActualEulerCoupling.spatialMatrix R θ (fun j=>(n j:ℝ)))
        (coefficient hR hθ s v n)+
      (c⁻¹:ℂ) • operator (ActualFourierSymbol.symbol hR hθ (fun j=>(n j:ℝ)))
        (coefficient hR hθ s v n)=0 := by
  apply original_equation_of_normalized hR hθ c (fun j=>(n j:ℝ))
  rw [root_coefficient,root_coefficient,differential_apply,map_smul,smul_smul,
    ←Complex.ofReal_mul,weight_shift]
  have hg := original_generator_radial hR hθ (direction n) c (radius n)
  rw [radial_coordinates] at hg
  rw [hg]
  have he : (attenuation n*weight s n)⁻¹*attenuation n=(weight s n)⁻¹ := by
    field_simp [(attenuation_positive n).ne',(weight_positive s n).ne']
  rw [he]

end
end Resonance.ActualSobolevDifferentiation
