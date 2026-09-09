import Resonance.ActualCompensatedDecay
import Resonance.ActualModeConjugacy

/-! The original, unnormalized five-moment mode equation and its original
Gram energy. All three matrix terms, the initial mode, and the clock are
retained in the exact conjugacy. -/
open Set ContinuousLinearMap
namespace Resonance.ActualOriginalModeDecay
noncomputable section
set_option maxHeartbeats 800000
open Thermodynamics MatrixHilbertDictionary ActualComplexNormalization
open ActualUniformHilbertData HilbertCompensatedGenerator FourierCompensationWeights
open ActualCompensatedDecay ActualModeConjugacy ActualGramHilbert
open ActualMassNormalization ActualEulerCoupling ActualFourierSymbol

theorem original_generator_radial {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (w : UnitDirection) (c r : ℝ) :
    ActualModeConjugacy.modeGenerator hR hθ c (r • (fun i=>w.val i))=
      ActualCompensatedDecay.modeGenerator hR hθ w c r := by
  rw [ActualModeConjugacy.modeGenerator,original_A_homogeneous,original_B_homogeneous]
  unfold ActualCompensatedDecay.modeGenerator generator damping
  simp only [smul_smul]
  congr 1
  · congr 1
    ring
  · congr 1
    push_cast
    rw [div_eq_mul_inv]
    ring

def gramEnergy (R : ℝ) (θ : Parameter) (v : H) : ℝ :=
  (inner ℂ v (operator (gramMatrix R θ) v)).re

theorem original_five_moment_mode_decay {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ : K,∀w : UnitDirection,∀c r T : ℝ,
      0<c → 0≤r → 0≤T → ∀u du : ℝ→H,
      (∀s∈Icc 0 T,HasDerivWithinAt u (du s) (Icc 0 T) s) →
      (∀s∈Icc 0 T,operator (gramMatrix R θ) (du s)+
        Complex.I • operator (spatialMatrix R θ (r • (fun i=>w.val i))) (u s)+
        (c⁻¹:ℂ) • operator (symbol hR (hpos θ.property) (r • (fun i=>w.val i))) (u s)=0) →
      gramEnergy R θ (u T)≤3*Real.exp (-δ*rate c r*T)*gramEnergy R θ (u 0) := by
  obtain ⟨δ,hδ,hd⟩ := original_normalized_forward_decay hR hK hpos
  refine ⟨δ,hδ,?_⟩
  intro θ w c r T hc hr hT u du hu heq
  have hy : ∀s∈Icc 0 T,HasDerivWithinAt (fun t=>rootOperator R θ (u t))
      (ActualCompensatedDecay.modeGenerator hR (hpos θ.property) w c r
        (rootOperator R θ (u s))) (Icc 0 T) s := by
    intro s hs
    have hh := original_mode_derivativeWithin hR (hpos θ.property) c (r • (fun i=>w.val i))
      (hu s hs) (heq s hs)
    rwa [original_generator_radial hR (hpos θ.property) w c r] at hh
  have hb := hd θ w c r T hc hr hT (fun s=>rootOperator R θ (u s)) hy
  simpa only [original_gram_norm hR (hpos θ.property),gramEnergy] using hb

end
end Resonance.ActualOriginalModeDecay
