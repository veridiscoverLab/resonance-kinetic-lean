import Resonance.CoordinateLevelGraph

/-! Exact coarea on each whole level of a genuine scalar coordinate chart.
The zero-level specialization is the original pinned Euclidean coarea. -/
open Set MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace Resonance.CoordinateLevelCoarea
noncomputable section
open PinnedMeasure CoordinateReplacement ControlledCoordinateChart
open LinearSurfaceArea C1GraphArea CoordinateLevelGraph RegularGraphCoarea

theorem gradient_partial {F : A → ℝ} {g : A → A}
    (hF : ∀z, HasFDerivAt F (innerSL ℝ (g z)) z) (p : A) :
    (fderiv ℝ F p) (CoordinateReplacement.unit 1)=g p 1 := by
  rw [(hF p).fderiv]
  simp [CoordinateReplacement.unit, PiLp.inner_apply,
    PlaneCoarea.real_inner_apply]

theorem source_level_integral {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z, HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : c≠0)
    (e : OpenPartialHomeomorph A A) (he : (e : A → A)=replace 1 F)
    (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (hn : ∀p∈e.source, (fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    (s : ℝ) {B : A → ℝ≥0∞} (hB : Measurable B) :
    (∫⁻p in e.source ∩ {p | F p=s}, B p ∂regularMeasure (fun p => F p-s) g c) =
      ∫⁻x in levelDomain e s, ENNReal.ofReal ((c*|g (graph (levelHeight e s) x) 1|)⁻¹) *
        B (graph (levelHeight e s) x) := by
  rw [source_level_eq_image e he s]
  apply graph_integral (fun p => (hF p).sub_const s) hg hc (levelDomain_open e s)
    (levelHeight_contDiffOn e hinv s) _ _ hB
  · intro x hx
    rw [level_graph_energy e he s hx, sub_self]
  · intro x hx
    have hp : graph (levelHeight e s) x∈e.source := by
      rw [level_graph_eq_inverse e he s hx]
      exact e.map_target hx
    simpa only [gradient_partial hF] using hn _ hp

theorem pinned_zero_measure {d : ℝ} :
    regularMeasure (fun p => liftedEnergy d p-0) (energyGradient d) ((2*Real.pi)^3) =
      PinnedMeasureNormalization.euclideanLiftedRegularCoarea d := by
  simp only [sub_zero]
  rfl

theorem pinned_chart_zero_integral {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (e : OpenPartialHomeomorph A A) (he : (e : A → A)=replace 1 (liftedEnergy d))
    (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (hn : ∀p∈e.source, (fderiv ℝ (liftedEnergy d) p) (CoordinateReplacement.unit 1)≠0)
    {B : A → ℝ≥0∞} (hB : Measurable B) :
    (∫⁻p in e.source ∩ {p | liftedEnergy d p=0}, B p
      ∂PinnedMeasureNormalization.euclideanLiftedRegularCoarea d) =
      ∫⁻x in levelDomain e 0,
        ENNReal.ofReal (((2*Real.pi)^3*|energyGradient d (graph (levelHeight e 0) x) 1|)⁻¹) *
          B (graph (levelHeight e 0) x) := by
  have h := source_level_integral (liftedEnergy_hasFDerivAt hd0 hdU)
    (energyGradient_continuous hd0 hdU).measurable (by positivity : (2*Real.pi)^3≠0)
    e he hinv hn 0 hB
  rw [pinned_zero_measure] at h
  exact h

theorem pinned_energy_contDiff_one {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    ContDiff ℝ 1 (liftedEnergy d) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hw := PinnedCharts.signed_omega_contDiff hdL hdU 1
  unfold liftedEnergy PinnedGeometry.energyDefect
  fun_prop

theorem pinned_regular_chart_exists {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (p : A) (hy : energyGradient d p 1≠0) :
    ∃ e : OpenPartialHomeomorph A A, ∃ r : ℝ,
      0<r ∧ e.source=Metric.ball p r ∧
      (e : A → A)=replace 1 (liftedEnergy d) ∧
      ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ (B : A → ℝ≥0∞), Measurable B →
        (∫⁻z in e.source ∩ {z | liftedEnergy d z=0}, B z
          ∂PinnedMeasureNormalization.euclideanLiftedRegularCoarea d) =
          ∫⁻x in levelDomain e 0,
            ENNReal.ofReal (((2*Real.pi)^3*
              |energyGradient d (graph (levelHeight e 0) x) 1|)⁻¹) *
                B (graph (levelHeight e 0) x) := by
  have hn : (fderiv ℝ (liftedEnergy d) p) (CoordinateReplacement.unit 1)≠0 := by
    simpa only [gradient_partial (liftedEnergy_hasFDerivAt hd0 hdU)] using hy
  obtain ⟨e,r,δ,he,hr,hδ,hsource,_hFsource,hinv,hjac⟩ :=
    ControlledCoordinateChart.exists_chart (pinned_energy_contDiff_one hd0 hdU).contDiffAt 1 hn
  refine ⟨e,r,hr,hsource,he,hinv,?_⟩
  intro B hB
  apply pinned_chart_zero_integral hd0 hdU e he hinv _ hB
  intro x hx
  exact abs_pos.mp (hδ.trans_le (hjac x hx))

end
end Resonance.CoordinateLevelCoarea
