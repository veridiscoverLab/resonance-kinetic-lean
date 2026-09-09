import Resonance.ActualSobolevSpace
import Resonance.ActualLatticeDecay
import Resonance.ActualModeReconstruction

/-! The actual constant five-moment evolution on every Fourier H^s,M
completion. All modes use the same original matrices and clock. -/
open Set
open scoped NNReal
namespace Resonance.ActualSobolevSemigroup
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert
open ActualSobolevSpace ActualCoefficientSemigroup ActualOriginalModeDecay
open PhysicalFourierFrequencies PhysicalScalarFourier ActualModeReconstruction
open HilbertExponentialFlow
variable {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
variable {c : ℝ} (hc : 0<c)

def evolution (s : ℝ) (t : ℝ≥0) : Sobolev s→L[ℂ]Sobolev s :=
  coefficientSemigroup hR hθ hc radius radius_nonneg direction t

theorem evolution_zero (s : ℝ) : evolution hR hθ hc s 0=1 :=
  coefficientSemigroup_zero hR hθ hc radius radius_nonneg direction

theorem evolution_add (s : ℝ) (t u : ℝ≥0) :
    evolution hR hθ hc s (t+u)=evolution hR hθ hc s t*evolution hR hθ hc s u :=
  coefficientSemigroup_add hR hθ hc radius radius_nonneg direction t u

theorem evolution_norm (s : ℝ) (t : ℝ≥0) : ‖evolution hR hθ hc s t‖≤Real.sqrt 3 :=
  coefficientSemigroup_norm hR hθ hc radius radius_nonneg direction t

theorem evolution_strong_continuous (s : ℝ) (v : Sobolev s) :
    Continuous (fun t:ℝ≥0=>evolution hR hθ hc s t v) :=
  coefficientSemigroup_strong_continuous hR hθ hc radius radius_nonneg direction v

theorem evolution_original_mode (s : ℝ) (t : ℝ≥0) (v : Sobolev s) (n : Frequency) :
    coefficient hR hθ s (evolution hR hθ hc s t v) n=
      physicalFlow hR hθ c (fun j=>(n j:ℝ)) t (coefficient hR hθ s v n) := by
  have hg := original_generator_radial hR hθ (direction n) c (radius n)
  rw [radial_coordinates] at hg
  rw [physicalFlow,root_coefficient,hg]
  simp only [coefficient,evolution,coefficientSemigroup_apply,map_smul]

theorem evolution_preserves_mean (s : ℝ) (t : ℝ≥0) (v : Sobolev s) :
    coefficient hR hθ s (evolution hR hθ hc s t v) 0=coefficient hR hθ s v 0 := by
  have hz : evolution hR hθ hc s t v 0=v 0 := by
    rw [evolution,coefficientSemigroup_apply,radius_zero]
    have hg : ActualCompensatedDecay.modeGenerator hR hθ (direction 0) c 0=0 := by
      simp [ActualCompensatedDecay.modeGenerator,HilbertCompensatedGenerator.generator,
        FourierCompensationWeights.damping]
    rw [hg]
    simp [flow,NormedSpace.exp_zero]
  simp only [coefficient,hz]

theorem sobolev_mean_zero_decay {K : Set Parameter} (hK : IsCompact K)
    (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ : K,∀c : ℝ,∀hc : 0<c,∀s : ℝ,∀t : ℝ≥0,
      ∀v : Sobolev s,coefficient hR (hpos θ.property) s v 0=0 →
      ‖evolution hR (hpos θ.property) hc s t v‖^2≤
        3*Real.exp (-δ*(c/(c^2+1))*t)*‖v‖^2 := by
  obtain ⟨δ,hδ,hd⟩ := ActualLatticeDecay.lattice_mean_zero_decay hR hK hpos
  refine ⟨δ,hδ,?_⟩
  intro θ c hc s t v hv
  have hh := congrArg (rootOperator R θ) hv
  rw [root_coefficient,map_zero] at hh
  have hz : v 0=0 := by
    have he := congrArg (fun z:H=>(weight s 0:ℂ) • z) hh
    simpa only [smul_smul,←Complex.ofReal_mul,mul_inv_cancel₀ (weight_positive s 0).ne',
      Complex.ofReal_one,one_smul,smul_zero] using he
  exact hd θ c hc t v hz

end
end Resonance.ActualSobolevSemigroup
