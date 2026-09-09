import Resonance.RegularChartAmplitude

/-! A genuine regular-chart approximate identity for the original energy
function. Both volume integrals and the layer reading are genuinely integrable. -/
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Resonance.RegularChartMollifier
noncomputable section
open PinnedMeasure CoordinateReplacement RegularChartAmplitude
open EnergyCoordinateFubini CompactLayerIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem ambient_weighted_integrable {A : Ambient → E} (hc : Continuous A)
    (hA : HasCompactSupport A) {ρ : ℝ → ℝ} (hρ : Integrable ρ) :
    Integrable (fun q=>ρ (q 1) • A q) := by
  apply (split_volume_preserving.symm.integrable_comp_emb split.symm.measurableEmbedding).mp
  have hi := weighted_joint_integrable (hc.comp split_symm_continuous)
    (split_compact_support hA) hρ
  convert hi using 1

omit [CompleteSpace E] in
theorem ambient_weighted_integral {A : Ambient → E} (hc : Continuous A)
    (hA : HasCompactSupport A) {ρ : ℝ → ℝ} (hρ : Integrable ρ) :
    ∫q,ρ (q 1) • A q=∫s,ρ s • layer (A ∘ split.symm) s := by
  rw [← split_volume_preserving.symm.integral_comp split.symm.measurableEmbedding]
  have hi := weighted_joint_integral (hc.comp split_symm_continuous)
    (split_compact_support hA) hρ
  convert hi using 1

omit [CompleteSpace E] in
theorem source_integrable {F : Ambient → ℝ} (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=replace 1 F) (hF : ContDiffOn ℝ 1 F e.source)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    {B : Ambient → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) {ρ : ℝ → ℝ} (hρ : Integrable ρ) :
    IntegrableOn (fun p=>ρ (F p) • B p) e.source := by
  have hd : ∀p∈e.source,DifferentiableAt ℝ F p := fun p hp=>
    (hF p hp |>.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt (by norm_num)
  apply (CoordinateBochnerChange.inverse_integrable_iff 1 e he hd hn _).mp
  have hr := amplitude_regular e hF hn hB hK hS
  have hi := (ambient_weighted_integrable hr.1 hr.2 hρ).integrableOn (s:=e.target)
  apply hi.congr
  filter_upwards [ae_restrict_mem e.open_target.measurableSet] with q hq
  rw [amplitude_formula e B hq,(ControlledCoordinateChart.coordinate_level_inverse e he hq).1]
  exact smul_comm _ _ _

theorem source_tendsto {F : Ambient → ℝ} (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=replace 1 F) (hF : ContDiffOn ℝ 1 F e.source)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    {B : Ambient → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) (ρ : ℝ → ℝ → ℝ)
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀x,0≤ρ η x)
    (hmass : ∀η,0<η→∫x,ρ η x=1)
    (hsupport : ∀η,0<η→∀x,ρ η x≠0→|x|≤η) :
    Tendsto (fun η=>∫p in e.source,ρ η (F p) • B p) (𝓝[>]0)
      (𝓝 (layer (amplitude F e B ∘ split.symm) 0)) := by
  have hr := amplitude_regular e hF hn hB hK hS
  have hd : ∀p∈e.source,DifferentiableAt ℝ F p := fun p hp=>
    (hF p hp |>.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt (by norm_num)
  have ht := arbitrary_kernel_layer_tendsto (hr.1.comp split_symm_continuous)
    (split_compact_support hr.2) ρ hρ hpos hmass hsupport
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [source_integral F e he hd hn B (ρ η),ambient_weighted_integral hr.1 hr.2 (hρ η hη)]

end
end Resonance.RegularChartMollifier
