import Resonance.CoordinateBochnerChange

/-! Reciprocal-Jacobian amplitudes for any actual coordinate replacement.
The source factor is retained before and after the coordinate change. -/
open Set MeasureTheory
open scoped ContDiff
namespace Resonance.CoordinateFactoredAmplitude
noncomputable section
open PinnedMeasure CoordinateReplacement ChartedCompactSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def amplitude (i : Fin 3) (F : Ambient → ℝ)
    (e : OpenPartialHomeomorph Ambient Ambient) (B : Ambient → E) : Ambient → E :=
  transport e (fun p=>|(fderiv ℝ F p) (unit i)|⁻¹ • B p)

theorem amplitude_regular (i : Fin 3) {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (hF : ContDiffOn ℝ 1 F e.source)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (unit i)≠0)
    {B : Ambient → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) :
    Continuous (amplitude i F e B) ∧ HasCompactSupport (amplitude i F e B) := by
  have hc : ContinuousOn (fun p=>|(fderiv ℝ F p) (unit i)|⁻¹) e.source :=
    (((hF.continuousOn_fderiv_of_isOpen e.open_source le_rfl).clm_apply
      continuousOn_const).abs).inv₀ (fun p hp=>abs_ne_zero.mpr (hn p hp))
  have hk : HasCompactSupport (fun p=>|(fderiv ℝ F p) (unit i)|⁻¹ • B p) := hK.smul_left
  have hs : tsupport (fun p=>|(fderiv ℝ F p) (unit i)|⁻¹ • B p)⊆e.source :=
    (tsupport_smul_subset_right _ _).trans hS
  exact ⟨transported_continuous e (hc.smul hB.continuousOn) hk hs,
    transported_compact_support e hk hs⟩

theorem factored_formula (i : Fin 3) {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (B : Ambient → E)
    (b : Ambient → ℝ) (a : Ambient → ℝ)
    (ha : ∀p∈e.source,a p=b (e p)) :
    amplitude i F e (fun p=>a p • B p)=fun q=>b q • amplitude i F e B q := by
  funext q
  by_cases hq : q∈e.target
  · simp only [amplitude,transport,Set.indicator_of_mem hq]
    rw [ha (e.symm q) (e.map_target hq),e.right_inv hq]
    exact smul_comm _ _ _
  · simp [amplitude,transport,hq]

theorem source_integral (i : Fin 3) {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (he : (e : Ambient → Ambient)=replace i F)
    (hF : ∀p∈e.source,DifferentiableAt ℝ F p)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (unit i)≠0)
    (B : Ambient → E) (ρ : Ambient → ℝ) :
    ∫p in e.source,ρ (e p) • B p = ∫q,ρ q • amplitude i F e B q := by
  rw [CoordinateBochnerChange.inverse_integral i e he hF hn]
  rw [←integral_indicator e.open_target.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q∈e.target
  · simp only [Set.indicator_of_mem hq,amplitude,transport,e.right_inv hq]
    exact smul_comm _ _ _
  · simp [amplitude,transport,hq]

theorem source_integrable_iff (i : Fin 3) {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (he : (e : Ambient → Ambient)=replace i F)
    (hF : ∀p∈e.source,DifferentiableAt ℝ F p)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (unit i)≠0)
    (B : Ambient → E) (ρ : Ambient → ℝ) :
    Integrable (fun q=>ρ q • amplitude i F e B q) ↔
      IntegrableOn (fun p=>ρ (e p) • B p) e.source := by
  have heq : (fun q=>ρ q • amplitude i F e B q)=e.target.indicator
      (fun q=>|(fderiv ℝ F (e.symm q)) (unit i)|⁻¹ • (ρ (e (e.symm q)) • B (e.symm q))) := by
    funext q
    by_cases hq : q∈e.target
    · simp only [amplitude,transport,Set.indicator_of_mem hq,e.right_inv hq]
      exact smul_comm _ _ _
    · simp [amplitude,transport,hq]
  rw [heq]
  change Integrable (e.target.indicator (fun q=>|(fderiv ℝ F (e.symm q)) (unit i)|⁻¹ •
    (ρ (e (e.symm q)) • B (e.symm q)))) (volume : Measure Ambient) ↔ _
  rw [integrable_indicator_iff e.open_target.measurableSet]
  exact CoordinateBochnerChange.inverse_integrable_iff i e he hF hn
    (fun p=>ρ (e p) • B p)

end
end Resonance.CoordinateFactoredAmplitude
