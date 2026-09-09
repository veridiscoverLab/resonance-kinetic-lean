import Resonance.ActualCompensatedDecay
import Resonance.FourierExponentialDecay

/-! The actual original normalized symbols satisfy the uniform exponential
bound. Its proof extracts all coercivity constants from the original matrices
on the singleton positive parameter set, not from a stability assumption. -/
open Set
namespace Resonance.ActualFourierExponential
noncomputable section
set_option maxHeartbeats 800000
open Thermodynamics MatrixHilbertDictionary ActualComplexNormalization
open ActualUniformHilbertData ActualCompensatedDecay HilbertExponentialFlow FourierExponentialDecay

set_option backward.isDefEq.respectTransparency false in
theorem original_exponential_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (w : UnitDirection) {c r t : ℝ}
    (hc : 0<c) (hr : 0≤r) (ht : 0≤t) :
    ‖flow (modeGenerator hR hθ w c r) t‖≤Real.sqrt 3 := by
  have hp : ({θ}:Set Parameter)⊆positiveDomain R := singleton_subset_iff.mpr hθ
  obtain ⟨β,k,L,hβ,hk,_,hdata⟩ := actual_uniform_hilbert_data hR isCompact_singleton hp
  obtain ⟨hA,hB,hb,hcoerc⟩ := hdata ⟨θ,mem_singleton θ⟩ w
  have hcoupling : k≤‖RankTwoHilbert.coupling (A R θ (fun i=>w.val i)) (e R θ)‖^2 := hb
  exact fourier_exponential_bound (A R θ (fun i=>w.val i)) (B hR hθ (fun i=>w.val i))
    (original_A_selfAdjoint hR hθ _) (original_B_selfAdjoint hR hθ _)
    (original_e_unit hR hθ) (original_B_mass_zero hR hθ (unit_direction_nonzero w))
    hβ hk hcoupling hcoerc hA hB hc hr ht

end
end Resonance.ActualFourierExponential
