import Resonance.WeightedGramRecovery
import Resonance.PhysicalMicroCoercivity

/-! Full physical H_nu recovery from the complete resonance difference
and a multiplier acting only on the fixed limit. This is the exact
five-kernel recovery interface used over the common time-space window. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ActualFullRecovery
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalMicroCoercivity
open WeightedGramRecovery LpOperators

theorem original_full_recovery_bound {R m M : ℝ} (hR : 0 < R) (hm : 0 < m) (hM : 0 ≤ M)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0 < C ∧ ∀ θ,(hθ : θ∈K) → ∀ b : E→ℝ,
      ∀ hb : MemLp b ∞ (referenceMeasure R),
      (∀ᵐ k ∂cubeVolume R,m ≤ b k ∧ b k ≤ M) → ∀ y u : Space R,
      analysisMap hR (hpos hθ) (multiplyCLM hb y)=0 → analysisMap hR (hpos hθ) u=0 →
      ‖y-u‖^2 ≤ C*(‖physicalDifference hR.le (hpos hθ) (y-u)‖^2+
        ‖(multiplyCLM hb-1) u‖^2) := by
  obtain ⟨C,hC,hrec⟩ := actual_uniform_moment_recovery hR hm hM hK hpos
  obtain ⟨δ,U,hδ,_hU,hco⟩ := actual_microcoercivity hR hK hpos
  refine ⟨2*C^2*(1+δ⁻¹),by positivity,?_⟩
  intro θ hθ b hb hbnd y u hmatch hu
  let g := (y-u)-projection hR (hpos hθ) (y-u)
  have hg : projection hR (hpos hθ) g=0 := by
    dsimp [g]
    rw [map_sub,projection_idempotent,sub_self]
  have hdiff : physicalDifference hR.le (hpos hθ) g=
      physicalDifference hR.le (hpos hθ) (y-u) := by
    dsimp [g]
    rw [map_sub,projection_difference_zero hR (hpos hθ),sub_zero]
  have hmicro := (hco θ hθ g hg).1
  rw [physical_form_square,hdiff] at hmicro
  have hgn : ‖g‖^2 ≤ δ⁻¹*‖physicalDifference hR.le (hpos hθ) (y-u)‖^2 := by
    rw [←div_eq_inv_mul,le_div_iff₀ hδ]
    simpa only [mul_comm δ] using hmicro
  have hr := hrec θ hθ b hb hbnd y u hmatch hu
  change ‖y-u‖ ≤ C*(‖g‖+‖(multiplyCLM hb-1) u‖) at hr
  have hs := pow_le_pow_left₀ (norm_nonneg (y-u)) hr 2
  have hsq : (‖g‖+‖(multiplyCLM hb-1) u‖)^2 ≤
      2*(‖g‖^2+‖(multiplyCLM hb-1) u‖^2) := by
    nlinarith [sq_nonneg (‖g‖-‖(multiplyCLM hb-1) u‖)]
  have hfirst : ‖y-u‖^2 ≤ 2*C^2*(‖g‖^2+‖(multiplyCLM hb-1) u‖^2) := by
    rw [mul_pow] at hs
    exact hs.trans ((mul_le_mul_of_nonneg_left hsq (sq_nonneg C)).trans_eq (by ring))
  apply hfirst.trans
  calc
    _ ≤ 2*C^2*(δ⁻¹*‖physicalDifference hR.le (hpos hθ) (y-u)‖^2+
        ‖(multiplyCLM hb-1) u‖^2) := by gcongr
    _ ≤ _ := by
      have hinv : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      nlinarith [mul_nonneg (sq_nonneg C)
        (sq_nonneg ‖physicalDifference hR.le (hpos hθ) (y-u)‖),
        mul_nonneg (mul_nonneg (sq_nonneg C) hinv) (sq_nonneg ‖(multiplyCLM hb-1) u‖)]

end
end Resonance.ActualFullRecovery
