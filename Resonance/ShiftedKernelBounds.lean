import Resonance.ShiftRowVanishing

/-! An actual reference envelope for the full signed normalized kernel,
retaining both original pair densities before the resolvent limit. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.ShiftedKernelBounds
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open NormalizedParameterAlgebra NormalizedPairParameterBounds LinftyParameterContinuity

theorem actual_kernel_reference_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀k∈cube R,∀p∈cube R,0<geometricFrequency R p →
      ‖AmbientLinftyCompact.kernel R θ k p‖≤C*baseRow R k p := by
  have hs : ({θ} : Set Parameter)⊆positiveDomain R := by
    intro β hβ
    simpa only [mem_singleton_iff.mp hβ] using hθ
  obtain ⟨A,Cd,hA,hCd,hden,hd⟩ := compact_denominator_bounds hR.le isCompact_singleton hs
  obtain ⟨B,hB,hb⟩ := PairParameterBounds.compact_pair_upper_bound hR.le isCompact_singleton hs
  refine ⟨(B/A)*(1+9*R^2),by positivity,?_⟩
  intro k hk p hp hg
  have hl := hden θ (mem_singleton θ) k hk p hp
  have hn : 0<normalDenominator R θ k p := (mul_pos hA hg).trans_le hl
  have hq {r t : ℝ} (hr : 0≤r) (ht : 0≤t) (hb : r≤B*t) :
      r/normalDenominator R θ k p≤(B/A)*(t/geometricFrequency R p) := by
    calc
      _ ≤ r/(A*geometricFrequency R p) := div_le_div_of_nonneg_left hr (mul_pos hA hg) hl
      _ ≤ (B*t)/(A*geometricFrequency R p) := div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have h1 := hq ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hb θ (mem_singleton θ) (k,p)).1
  have h2 := hq ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hb θ (mem_singleton θ) (k,p)).2
  have hin : 0≤(IncomingPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p := by positivity
  have hcr : 0≤2*((CrossPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p) := by positivity
  change ‖(IncomingPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p-
    2*((CrossPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p)‖≤_
  calc
    _ ≤ ‖(IncomingPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p‖+
      ‖2*((CrossPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p)‖ := norm_sub_le _ _
    _ ≤ (B/A)*(baseDensity R k p/geometricFrequency R p) := by
      rw [Real.norm_of_nonneg hin,Real.norm_of_nonneg hcr]
      calc
        _ ≤ (B/A)*((IncomingPairDensity.density R (weight JointWeightComparison.unitParameter) (k,p)).toReal/geometricFrequency R p)+
          2*((B/A)*((CrossPairDensity.density R (weight JointWeightComparison.unitParameter) (k,p)).toReal/geometricFrequency R p)) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = _ := by unfold baseDensity; ring
    _ ≤ (B/A)*((1+9*R^2)*(baseDensity R k p/referenceFrequency R p)) :=
      mul_le_mul_of_nonneg_left (geometric_inverse_comparison hR.le hp hg (baseDensity_nonnegative R k p)) (by positivity)
    _ = _ := by unfold baseRow; ring

end
end Resonance.ShiftedKernelBounds
