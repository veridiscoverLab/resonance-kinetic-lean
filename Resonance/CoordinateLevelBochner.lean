import Resonance.RegularGraphBochner
import Resonance.RegularChartMollifier

/-! Exact signed coarea readings of an entire level of the same energy chart.
The normalization and the compact layer reading are kept in a single identity. -/
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace Resonance.CoordinateLevelBochner
noncomputable section
open LinearSurfaceArea C1GraphArea CoordinateReplacement CoordinateLevelGraph
open CoordinateLevelCoarea RegularGraphCoarea RegularChartAmplitude
open EnergyCoordinateFubini CompactLayerIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem level_amplitude {F : A → ℝ} {g : A → A}
    (hF : ∀p,HasFDerivAt F (innerSL ℝ (g p)) p)
    (e : OpenPartialHomeomorph A A) (he : (e : A → A)=replace 1 F)
    (B : A → E) (s : ℝ) (x : P) :
    amplitude F e B (levelEmbedding s x)=
      (levelDomain e s).indicator
        (fun y=>|g (graph (levelHeight e s) y) 1|⁻¹ • B (graph (levelHeight e s) y)) x := by
  by_cases hx : x∈levelDomain e s
  · rw [Set.indicator_of_mem hx,amplitude_formula e B hx,
      gradient_partial hF,level_graph_eq_inverse e he s hx]
  · have ht : levelEmbedding s x∉e.target := hx
    simp [amplitude,ChartedCompactSupport.transport,ht,hx]

theorem source_level_integral {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀p,HasFDerivAt F (innerSL ℝ (g p)) p) (hg : Measurable g) (hc : 0<c)
    (e : OpenPartialHomeomorph A A) (he : (e : A → A)=replace 1 F)
    (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    (B : A → E) (s : ℝ) :
    ∫p in e.source∩{p|F p=s},B p ∂regularMeasure (fun p=>F p-s) g c =
      c⁻¹ • layer (amplitude F e B ∘ split.symm) s := by
  rw [source_level_eq_image e he s]
  have hz : ∀x∈levelDomain e s,F (graph (levelHeight e s) x)-s=0 := by
    intro x hx
    rw [level_graph_energy e he s hx,sub_self]
  have hy : ∀x∈levelDomain e s,g (graph (levelHeight e s) x) 1≠0 := by
    intro x hx
    have hp := e.map_target hx
    rw [←level_graph_eq_inverse e he s hx] at hp
    simpa only [gradient_partial hF] using hn _ hp
  rw [RegularGraphBochner.local_graph_integral (fun p=>(hF p).sub_const s) hg hc
    (levelDomain_open e s) (levelHeight_contDiffOn e hinv s) hz hy]
  have hread : layer (amplitude F e B ∘ split.symm) s =
      ∫x in levelDomain e s,|g (graph (levelHeight e s) x) 1|⁻¹ • B (graph (levelHeight e s) x) := by
    unfold layer
    simp only [Function.comp_apply,split_symm_apply]
    simp_rw [level_amplitude hF e he B s]
    exact integral_indicator (levelDomain_open e s).measurableSet
  rw [hread,←integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smul_smul,mul_inv_rev,mul_comm]

theorem source_level_integrable {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀p,HasFDerivAt F (innerSL ℝ (g p)) p) (hg : Measurable g) (hc : 0<c)
    (e : OpenPartialHomeomorph A A) (he : (e : A → A)=replace 1 F)
    (hFC : ContDiffOn ℝ 1 F e.source) (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    {B : A → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) (s : ℝ) :
    IntegrableOn B (e.source∩{p|F p=s}) (regularMeasure (fun p=>F p-s) g c) := by
  rw [source_level_eq_image e he s]
  have hz : ∀x∈levelDomain e s,F (graph (levelHeight e s) x)-s=0 := by
    intro x hx
    rw [level_graph_energy e he s hx,sub_self]
  have hy : ∀x∈levelDomain e s,g (graph (levelHeight e s) x) 1≠0 := by
    intro x hx
    have hp := e.map_target hx
    rw [←level_graph_eq_inverse e he s hx] at hp
    simpa only [gradient_partial hF] using hn _ hp
  apply (RegularGraphBochner.local_graph_integrable_iff (fun p=>(hF p).sub_const s) hg hc
    (levelDomain_open e s) (levelHeight_contDiffOn e hinv s) hz hy B).mpr
  have hr := amplitude_regular e hFC hn hB hK hS
  have hi := slice_integrable (hr.1.comp split_symm_continuous)
    (split_compact_support hr.2) s
  simp only [Function.comp_apply,split_symm_apply] at hi
  simp_rw [level_amplitude hF e he B s] at hi
  have hj := (integrable_indicator_iff (levelDomain_open e s).measurableSet).mp hi
  have hsm : Integrable (fun x=>c⁻¹ • (|g (graph (levelHeight e s) x) 1|⁻¹ •
      B (graph (levelHeight e s) x))) (volume.restrict (levelDomain e s)) := hj.smul (c⁻¹)
  apply hsm.congr
  filter_upwards [] with x
  rw [smul_smul,mul_inv_rev,mul_comm]

end
end Resonance.CoordinateLevelBochner
