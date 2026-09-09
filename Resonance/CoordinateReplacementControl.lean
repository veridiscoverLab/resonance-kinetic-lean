import Resonance.CoordinateReplacement

/-! A compact source neighborhood for the actual inverse-function chart.
Derivative control is derived from C1 regularity, not added as a new premise. -/
open Set Filter
open scoped Topology ContDiff
namespace Resonance.CoordinateReplacementControl
noncomputable section
open PinnedMeasure CoordinateReplacement

theorem compact_controlled_coordinate {F : Ambient → ℝ} {p : Ambient}
    (hF : ContDiffAt ℝ 1 F p) (i : Fin 3)
    (hn : (fderiv ℝ F p) (CoordinateReplacement.unit i)≠0) :
    ∃ e : OpenPartialHomeomorph Ambient Ambient, ∃ r δ : ℝ,
      (e : Ambient → Ambient)=replace i F ∧ 0<r ∧ 0<δ ∧
      Metric.closedBall p r⊆e.source ∧
      (∀x∈Metric.closedBall p r, δ≤|(fderiv ℝ F x) (CoordinateReplacement.unit i)|) ∧
      ContDiffOn ℝ 1 F (Metric.closedBall p r) ∧
      ContDiffOn ℝ 1 e.symm (e '' Metric.closedBall p r) := by
  obtain ⟨e,he,hsource,hinv⟩ := local_coordinate_exists hF i hn
  let δ := |(fderiv ℝ F p) (CoordinateReplacement.unit i)|/2
  have hδ : 0<δ := half_pos (abs_pos.mpr hn)
  have hδlt : δ < |(fderiv ℝ F p) (CoordinateReplacement.unit i)| :=
    half_lt_self (abs_pos.mpr hn)
  have hJ : ContinuousAt (fun x => |(fderiv ℝ F x) (CoordinateReplacement.unit i)|) p :=
    ((hF.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).abs
  have hJnear : ∀ᶠx in 𝓝 p, δ < |(fderiv ℝ F x) (CoordinateReplacement.unit i)| :=
    hJ.eventually (Ioi_mem_nhds hδlt)
  have hInvNear : ∀ᶠx in 𝓝 p, ContDiffAt ℝ 1 e.symm (e x) :=
    (e.continuousAt hsource).tendsto.eventually (hinv.eventually (by norm_num))
  have hFnear : ∀ᶠx in 𝓝 p, ContDiffAt ℝ 1 F x := hF.eventually (by norm_num)
  have hsourceNear : ∀ᶠx in 𝓝 p, x∈e.source := e.open_source.mem_nhds hsource
  have hall : ∀ᶠx in 𝓝 p, x∈e.source ∧
      δ < |(fderiv ℝ F x) (CoordinateReplacement.unit i)| ∧
      ContDiffAt ℝ 1 F x ∧ ContDiffAt ℝ 1 e.symm (e x) :=
    hsourceNear.and (hJnear.and (hFnear.and hInvNear))
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp hall
  have hsub : Metric.closedBall p (s/2)⊆{x | x∈e.source ∧
      δ < |(fderiv ℝ F x) (CoordinateReplacement.unit i)| ∧
      ContDiffAt ℝ 1 F x ∧ ContDiffAt ℝ 1 e.symm (e x)} :=
    (Metric.closedBall_subset_ball (half_lt_self hs)).trans hball
  refine ⟨e,s/2,δ,he,half_pos hs,hδ,fun x hx => (hsub hx).1,
    fun x hx => (hsub hx).2.1.le,fun x hx => (hsub hx).2.2.1.contDiffWithinAt,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact (hsub hx).2.2.2.contDiffWithinAt

end
end Resonance.CoordinateReplacementControl
