import Resonance.PhysicalNormalizedSemigroup
import Resonance.FourierEnergySummation

/-! Decay on the entire original integer lattice. The zero mode is kept
and its five-component vanishing is imposed only for the mean-zero estimate. -/
open Set
open scoped NNReal
namespace Resonance.ActualLatticeDecay
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualCompensatedDecay
open ActualCoefficientSemigroup PhysicalFourierFrequencies PhysicalScalarFourier
open HilbertExponentialFlow FourierCompensationWeights L2DiagonalOperator

theorem lattice_mode_decay {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ : K,∀c : ℝ,∀hc : 0<c,∀t : ℝ≥0,
      ∀v : Space Frequency H,∀n : Frequency,
      ‖coefficientSemigroup hR (hpos θ.property) hc radius radius_nonneg direction t v n‖^2
      ≤3*Real.exp (-δ*rate c (radius n)*t)*‖v n‖^2 := by
  obtain ⟨δ,hδ,hdec⟩ := original_normalized_forward_decay hR hK hpos
  refine ⟨δ,hδ,?_⟩
  intro θ c hc t v n
  let G := modeGenerator hR (hpos θ.property) (direction n) c (radius n)
  have hh := hdec θ (direction n) c (radius n) t hc (radius_nonneg n) t.property
    (fun s=>flow G s (v n)) (fun s _=>(flow_hasDerivAt G (v n) s).hasDerivWithinAt)
  simpa only [coefficientSemigroup_apply,G,flow_zero,ContinuousLinearMap.one_apply] using hh

theorem lattice_mean_zero_decay {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ : K,∀c : ℝ,∀hc : 0<c,∀t : ℝ≥0,
      ∀v : Space Frequency H,v 0=0 →
      ‖coefficientSemigroup hR (hpos θ.property) hc radius radius_nonneg direction t v‖^2
      ≤3*Real.exp (-δ*(c/(c^2+1))*t)*‖v‖^2 := by
  obtain ⟨δ,hδ,hdec⟩ := lattice_mode_decay hR hK hpos
  refine ⟨δ,hδ,?_⟩
  intro θ c hc t v hv
  let w := coefficientSemigroup hR (hpos θ.property) hc radius radius_nonneg direction t v
  let C := 3*Real.exp (-δ*(c/(c^2+1))*t)
  have hi : ∀n,‖w n‖^2≤C*‖v n‖^2 := by
    intro n
    by_cases hn:n=0
    · subst n
      simp [w,coefficientSemigroup_apply,hv]
    · have hr := FourierEnergySummation.rate_lower_nonzero hc (radius_lower hn)
      have he : Real.exp (-δ*rate c (radius n)*t)≤Real.exp (-δ*(c/(c^2+1))*t) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonpos_left hr (neg_nonpos.mpr hδ.le)) t.property
      have hb := hdec θ c hc t v n
      have hm := mul_le_mul_of_nonneg_right he (show 0≤3*‖v n‖^2 by positivity)
      dsimp [w,C]
      nlinarith
  have hs := Summable.tsum_le_tsum hi (hasSum_norm_square w).summable
    ((hasSum_norm_square v).summable.mul_left C)
  rw [(hasSum_norm_square w).tsum_eq,tsum_mul_left,(hasSum_norm_square v).tsum_eq] at hs
  exact hs

end
end Resonance.ActualLatticeDecay
