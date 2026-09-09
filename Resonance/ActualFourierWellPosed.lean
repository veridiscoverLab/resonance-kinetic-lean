import Resonance.ActualModeUniqueness
import Resonance.ActualSobolevSemigroup

/-! Original integer-frequency and whole Sobolev solution statements.
The full field u is fixed before all frequency tests are quantified. -/
open Set
open scoped NNReal
namespace Resonance.ActualFourierWellPosed
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualEulerCoupling ActualFourierSymbol
open ActualOriginalModeDecay ActualModeUniqueness ActualModeReconstruction
open ActualSobolevSpace ActualSobolevSemigroup PhysicalFourierFrequencies PhysicalScalarFourier

theorem original_integer_mode_decay {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ : K,∀c : ℝ,0<c → ∀n : Frequency,∀T : ℝ,0≤T →
      ∀u du : ℝ→H,
      (∀t∈Icc 0 T,HasDerivWithinAt u (du t) (Icc 0 T) t) →
      (∀t∈Icc 0 T,operator (gramMatrix R θ) (du t)+
        Complex.I • operator (spatialMatrix R θ (fun j=>(n j:ℝ))) (u t)+
        (c⁻¹:ℂ) • operator (symbol hR (hpos θ.property) (fun j=>(n j:ℝ))) (u t)=0) →
      gramEnergy R θ (u T)≤3*Real.exp (-δ*FourierCompensationWeights.rate c (radius n)*T)*
        gramEnergy R θ (u 0) := by
  obtain ⟨δ,hδ,hd⟩ := original_five_moment_mode_decay hR hK hpos
  refine ⟨δ,hδ,?_⟩
  intro θ c hc n T hT u du hu heq
  apply hd θ (direction n) c (radius n) T hc (radius_nonneg n) hT u du hu
  simpa only [radial_coordinates] using heq

theorem original_sobolev_forward_unique {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ) (T : ℝ≥0)
    (u : ℝ→Sobolev s) (du : Frequency→ℝ→H)
    (hu : ∀n:Frequency,∀t∈Icc 0 (T:ℝ),HasDerivWithinAt
      (fun z=>coefficient hR hθ s (u z) n) (du n t) (Icc 0 (T:ℝ)) t)
    (heq : ∀n:Frequency,∀t∈Icc 0 (T:ℝ),operator (gramMatrix R θ) (du n t)+
      Complex.I • operator (spatialMatrix R θ (fun j=>(n j:ℝ))) (coefficient hR hθ s (u t) n)+
      (c⁻¹:ℂ) • operator (symbol hR hθ (fun j=>(n j:ℝ))) (coefficient hR hθ s (u t) n)=0) :
    u T=evolution hR hθ hc s T (u 0) := by
  apply coefficient_injective hR hθ s
  funext n
  rw [evolution_original_mode]
  exact original_forward_solution_unique hR hθ c (fun j=>(n j:ℝ)) T.property
    (fun t=>coefficient hR hθ s (u t) n) (du n) (hu n) (heq n)

end
end Resonance.ActualFourierWellPosed
