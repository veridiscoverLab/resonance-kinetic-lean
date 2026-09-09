import Resonance.ActualUniformHilbertData
import Resonance.FourierForwardDecay

/-! The original normalized five-moment Fourier modes. Uniform decay is
derived on every compact positive RJ parameter set; no spectral gap,
compensator, or uniform matrix bound is an input assumption. -/
open Set
namespace Resonance.ActualCompensatedDecay
noncomputable section
set_option maxHeartbeats 1000000
open Thermodynamics MatrixHilbertDictionary ActualComplexNormalization
open ActualUniformHilbertData HilbertCompensatedGenerator FourierCompensationWeights
open UniformHilbertCompensation FourierForwardDecay

def modeGenerator {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (w : UnitDirection) (c r : ℝ) : H→L[ℂ]H :=
  generator (A R θ (fun i=>w.val i)) (B hR hθ (fun i=>w.val i)) r (damping c r)

set_option backward.isDefEq.respectTransparency false in
theorem original_normalized_forward_decay {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ : K,∀w : UnitDirection,∀c r T : ℝ,
      0<c → 0≤r → 0≤T → ∀u : ℝ→H,
      (∀s∈Icc 0 T,HasDerivWithinAt u
        (modeGenerator hR (hpos θ.property) w c r (u s)) (Icc 0 T) s) →
      ‖u T‖^2≤3*Real.exp (-δ*rate c r*T)*‖u 0‖^2 := by
  obtain ⟨β,k,L,hβ,hk,hL,hdata⟩ := actual_uniform_hilbert_data hR hK hpos
  refine ⟨2*decayBudget β k L/3,by
    have hp := decayBudget_positive hβ hk hL.le
    positivity,?_⟩
  intro θ w c r T hc hr hT u hu
  obtain ⟨hA,hB,hb,hcoerc⟩ := hdata θ w
  have hcoupling : k≤‖RankTwoHilbert.coupling (A R θ (fun i=>w.val i)) (e R θ)‖^2 := hb
  exact fourier_forward_decay (A R θ (fun i=>w.val i)) (B hR (hpos θ.property) (fun i=>w.val i))
    (original_A_selfAdjoint hR (hpos θ.property) _)
    (original_B_selfAdjoint hR (hpos θ.property) _)
    (original_e_unit hR (hpos θ.property))
    (original_B_mass_zero hR (hpos θ.property) (unit_direction_nonzero w))
    hβ hk hcoupling hcoerc hA hB hc hr hT hu

end
end Resonance.ActualCompensatedDecay
