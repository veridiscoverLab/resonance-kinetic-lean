import Resonance.CoordinateFactoredAmplitude

/-! The reciprocal-Jacobian amplitude needs source regularity only on the
actual chart. A compact zero extension does not assume inverse continuity
outside the chart or regularity of a quotient through its zero denominator. -/
open Set
open scoped ContDiff
namespace Resonance.CoordinateAmplitudeOn
noncomputable section
open PinnedMeasure CoordinateReplacement ChartedCompactSupport CoordinateFactoredAmplitude
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem amplitude_regular_on (i : Fin 3) {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (hF : ContDiffOn ℝ 1 F e.source)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (unit i)≠0)
    {B : Ambient → E} (hB : ContinuousOn B e.source) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) :
    Continuous (amplitude i F e B) ∧ HasCompactSupport (amplitude i F e B) := by
  have hc : ContinuousOn (fun p=>|(fderiv ℝ F p) (unit i)|⁻¹) e.source :=
    (((hF.continuousOn_fderiv_of_isOpen e.open_source le_rfl).clm_apply
      continuousOn_const).abs).inv₀ (fun p hp=>abs_ne_zero.mpr (hn p hp))
  have hk : HasCompactSupport (fun p=>|(fderiv ℝ F p) (unit i)|⁻¹ • B p) := hK.smul_left
  have hs : tsupport (fun p=>|(fderiv ℝ F p) (unit i)|⁻¹ • B p)⊆e.source :=
    (tsupport_smul_subset_right _ _).trans hS
  exact ⟨transported_continuous e (hc.smul hB) hk hs,
    transported_compact_support e hk hs⟩

end
end Resonance.CoordinateAmplitudeOn
