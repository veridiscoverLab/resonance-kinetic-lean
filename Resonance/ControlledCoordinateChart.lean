import Resonance.CoordinateReplacementControl

/-! A genuine coordinate chart whose whole source and target satisfy the
regularity used in local integral changes of variables. -/
open Set
open scoped Topology ContDiff
namespace Resonance.ControlledCoordinateChart
noncomputable section
open PinnedMeasure CoordinateReplacement CoordinateReplacementControl

theorem exists_chart {F : Ambient → ℝ} {p : Ambient}
    (hF : ContDiffAt ℝ 1 F p) (i : Fin 3)
    (hn : (fderiv ℝ F p) (CoordinateReplacement.unit i)≠0) :
    ∃ e : OpenPartialHomeomorph Ambient Ambient, ∃ r δ : ℝ,
      (e : Ambient → Ambient)=replace i F ∧ 0<r ∧ 0<δ ∧
      e.source=Metric.ball p r ∧ ContDiffOn ℝ 1 F e.source ∧
      ContDiffOn ℝ 1 e.symm e.target ∧
      ∀x∈e.source, δ≤|(fderiv ℝ F x) (CoordinateReplacement.unit i)| := by
  obtain ⟨e,r,δ,he,hr,hδ,hsource,hjac,hFsource,hInv⟩ := compact_controlled_coordinate hF i hn
  let e0 := e.restr (Metric.ball p r)
  have hes : e0.source=Metric.ball p r := by
    rw [e.restr_source' _ Metric.isOpen_ball]
    exact inter_eq_right.mpr (Metric.ball_subset_closedBall.trans hsource)
  have htarget : e0.target⊆e '' Metric.closedBall p r := by
    intro y hy
    have hx : e0.symm y∈Metric.ball p r := by rw [←hes]; exact e0.map_target hy
    exact ⟨e0.symm y, Metric.ball_subset_closedBall hx, e0.right_inv hy⟩
  refine ⟨e0,r,δ,he,hr,hδ,hes,?_,hInv.mono htarget,?_⟩
  · rw [hes]
    exact hFsource.mono Metric.ball_subset_closedBall
  · intro x hx
    rw [hes] at hx
    exact hjac x (Metric.ball_subset_closedBall hx)

theorem coordinate_level_inverse {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (he : (e : Ambient → Ambient)=replace 1 F)
    {q : Ambient} (hq : q∈e.target) :
    F (e.symm q)=q 1 ∧ (e.symm q) 0=q 0 ∧ (e.symm q) 2=q 2 := by
  have hi : replace 1 F (e.symm q)=q := by rw [←he]; exact e.right_inv hq
  have h0 := congrArg (fun p : Ambient => p 0) hi
  have h1 := congrArg (fun p : Ambient => p 1) hi
  have h2 := congrArg (fun p : Ambient => p 2) hi
  refine ⟨?_,?_,?_⟩
  · simpa only [replace_apply, if_pos rfl] using h1
  · simpa [replace_apply] using h0
  · simpa [replace_apply, show (2:Fin 3)≠1 by decide] using h2

end
end Resonance.ControlledCoordinateChart
