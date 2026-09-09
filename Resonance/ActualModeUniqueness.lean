import Resonance.ActualModeReconstruction
import Resonance.HilbertFlowReality

/-! Uniqueness for any forward solution of the original M/J/D mode
equation; no extension to negative times is required. -/
open Set
namespace Resonance.ActualModeUniqueness
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert ActualModeConjugacy
open ActualModeReconstruction ActualEulerCoupling ActualFourierSymbol
open HilbertExponentialFlow HilbertFlowReality

theorem original_forward_solution_unique {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (c : ℝ) (ell : Fin 3→ℝ) {T : ℝ} (hT : 0≤T)
    (u du : ℝ→H)
    (hu : ∀t∈Icc 0 T,HasDerivWithinAt u (du t) (Icc 0 T) t)
    (heq : ∀t∈Icc 0 T,operator (gramMatrix R θ) (du t)+
      Complex.I • operator (spatialMatrix R θ ell) (u t)+
      (c⁻¹:ℂ) • operator (symbol hR hθ ell) (u t)=0) :
    u T=physicalFlow hR hθ c ell T (u 0) := by
  let G := modeGenerator hR hθ c ell
  let z := fun t=>rootOperator R θ (u t)-flow G t (rootOperator R θ (u 0))
  have hz : ∀t∈Icc 0 T,HasDerivWithinAt z (G (z t)) (Icc 0 T) t := by
    intro t ht
    have h1 := original_mode_derivativeWithin hR hθ c ell (hu t ht) (heq t ht)
    have h2 := (flow_hasDerivAt G (rootOperator R θ (u 0)) t).hasDerivWithinAt (s:=Icc 0 T)
    have hh := h1.sub h2
    simpa only [z,G,map_sub] using hh
  have h0 : z 0=0 := by simp [z,flow_zero]
  have hh := sub_eq_zero.mp (forward_zero_unique G hT hz h0)
  have he := congrArg (inverseOperator R θ) hh
  have hi : ∀w:H,inverseOperator R θ (rootOperator R θ w)=w := by
    intro w
    exact DFunLike.congr_fun (original_inverse_root hR hθ) w
  simpa only [hi,physicalFlow,G] using he

end
end Resonance.ActualModeUniqueness
