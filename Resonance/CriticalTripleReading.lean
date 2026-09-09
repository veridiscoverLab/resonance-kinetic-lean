import Resonance.CriticalTripleMollifier
import Resonance.CriticalSourceCutoff
import Resonance.CompactLayerIntegral

/-! Absolute integrability and removal of the shared-factor cutoff in the
explicit critical reading. This is separate from its coarea identification. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CriticalTripleReading
noncomputable section
open LinearSurfaceArea CriticalCoordinateFubini
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def planeFactor (x : P) : ℝ := x 0*x 1

theorem planeFactor_continuous : Continuous planeFactor :=
  (PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 0).mul
    (PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 1)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem slice_integrable {B : A → E} (hc : Continuous B) (hK : HasCompactSupport B) :
    Integrable (fun x : P=>B (CriticalCoordinateFubini.join x 0)) := by
  have hcomp := hc.comp split_symm_continuous
  have hcompact := split_compact_support hK
  have hs : HasCompactSupport (fun x : P=>(B ∘ split.symm) (x,0)) := by
    apply HasCompactSupport.of_support_subset_isCompact (hcompact.image continuous_fst)
    intro x hx
    exact ⟨(x,0),subset_tsupport _ hx,rfl⟩
  have hi : Integrable (fun x : P=>(B ∘ split.symm) (x,0)) (volume : Measure P) :=
    (hcomp.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hs
  simpa only [Function.comp_apply,split_symm_apply] using hi

omit [CompleteSpace E] in
theorem reading_integrable {B : A → E} (hc : Continuous B) (hK : HasCompactSupport B) :
    Integrable (fun x : P=>(planeFactor x/|planeFactor x|) • B (CriticalCoordinateFubini.join x 0)) := by
  have hi := slice_integrable hc hK
  apply hi.norm.mono' (((planeFactor_continuous.measurable.div
    planeFactor_continuous.abs.measurable).aestronglyMeasurable).smul hi.aestronglyMeasurable)
  filter_upwards [] with x
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_abs]
  by_cases hx : planeFactor x=0
  · simp [hx]
  · simp [div_self (abs_ne_zero.mpr hx)]

theorem cutoff_reading_tendsto {B : A → E} (hc : Continuous B) (hK : HasCompactSupport B) :
    Tendsto (fun δ=>CriticalTripleMollifier.reading
      (fun p=>CriticalSourceCutoff.cutoff δ (p 1*p 2) • B p)) (𝓝[>]0)
      (𝓝 (CriticalTripleMollifier.reading B)) := by
  have ht := CriticalSourceCutoff.integral_tendsto planeFactor_continuous.measurable
    (reading_integrable hc hK) (ae_of_all volume (fun x hx=>by simp [hx]))
  apply ht.congr
  intro δ
  apply integral_congr_ae
  filter_upwards [] with x
  change CriticalSourceCutoff.cutoff δ (planeFactor x) •
    ((planeFactor x/|planeFactor x|) • B (CriticalCoordinateFubini.join x 0)) =
    (planeFactor x/|planeFactor x|) •
      (CriticalSourceCutoff.cutoff δ (planeFactor x) • B (CriticalCoordinateFubini.join x 0))
  exact smul_comm _ _ _

end
end Resonance.CriticalTripleReading
