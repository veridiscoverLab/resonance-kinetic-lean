import Resonance.CoordinateBochnerChange
import Resonance.CoordinateLevelCoarea
import Resonance.CompactLayerIntegral

/-! The actual reciprocal-Jacobian source amplitude on a regular energy chart.
Zero extension is justified by the original compact source support. -/
open Set MeasureTheory
open scoped ContDiff
namespace Resonance.RegularChartAmplitude
noncomputable section
open PinnedMeasure CoordinateReplacement ChartedCompactSupport
open EnergyCoordinateFubini CoordinateLevelGraph
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def amplitude (F : Ambient → ℝ) (e : OpenPartialHomeomorph Ambient Ambient)
    (B : Ambient → E) : Ambient → E :=
  transport e (fun p => |(fderiv ℝ F p) (CoordinateReplacement.unit 1)|⁻¹ • B p)

theorem amplitude_regular {F : Ambient → ℝ} (e : OpenPartialHomeomorph Ambient Ambient)
    (hF : ContDiffOn ℝ 1 F e.source)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    {B : Ambient → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) :
    Continuous (amplitude F e B) ∧ HasCompactSupport (amplitude F e B) := by
  have hc : ContinuousOn (fun p=>|(fderiv ℝ F p) (CoordinateReplacement.unit 1)|⁻¹)
      e.source :=
    (((hF.continuousOn_fderiv_of_isOpen e.open_source le_rfl).clm_apply
      continuousOn_const).abs).inv₀ (fun p hp=>abs_ne_zero.mpr (hn p hp))
  have hk : HasCompactSupport (fun p=>|(fderiv ℝ F p) (CoordinateReplacement.unit 1)|⁻¹ • B p) :=
    hK.smul_left
  have hs : tsupport (fun p=>|(fderiv ℝ F p) (CoordinateReplacement.unit 1)|⁻¹ • B p)⊆e.source :=
    (tsupport_smul_subset_right _ _).trans hS
  exact ⟨transported_continuous e (hc.smul hB.continuousOn) hk hs,
    transported_compact_support e hk hs⟩

theorem amplitude_formula {F : Ambient → ℝ} (e : OpenPartialHomeomorph Ambient Ambient)
    (B : Ambient → E) {q : Ambient} (hq : q∈e.target) :
    amplitude F e B q=|(fderiv ℝ F (e.symm q)) (CoordinateReplacement.unit 1)|⁻¹ • B (e.symm q) := by
  simp [amplitude,transport,hq]

theorem source_integral (F : Ambient → ℝ) (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=replace 1 F)
    (hF : ∀p∈e.source,DifferentiableAt ℝ F p)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    (B : Ambient → E) (ρ : ℝ → ℝ) :
    ∫p in e.source,ρ (F p) • B p = ∫q,ρ (q 1) • amplitude F e B q := by
  rw [CoordinateBochnerChange.inverse_integral 1 e he hF hn]
  rw [← integral_indicator e.open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q∈e.target
  · rw [Set.indicator_of_mem hq,amplitude_formula e B hq,
      (ControlledCoordinateChart.coordinate_level_inverse e he hq).1]
    exact smul_comm _ _ _
  · simp [amplitude,transport,hq]

end
end Resonance.RegularChartAmplitude
