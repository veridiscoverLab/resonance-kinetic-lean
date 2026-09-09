import Resonance.ProjectionFormStability

/-! A finite orthogonal approximation is constructed from the actual
compact image of the unit ball, not postulated as a stability premise. -/
open Set Metric
open scoped InnerProductSpace
namespace Resonance.CompactOrthogonalApproximation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 1800000

def spanProjection (s : Finset E) : E→L[ℝ]E :=
  (Submodule.span ℝ (s:Set E)).starProjection

theorem compact_range_projection (K : E→L[ℝ]E) (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0<ε) :
    ∃s:Finset E, ‖K-(spanProjection s).comp K‖≤ε := by
  obtain ⟨S,hS,hKS⟩:=hK.image_closedBall_subset_compact (f:=K.toLinearMap) 1
  obtain ⟨t,_,ht,hcover⟩:=hS.finite_cover_balls hε
  refine ⟨ht.toFinset,?_⟩
  let W:=Submodule.span ℝ (ht.toFinset:Set E)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  have hxs:K x∈S:=hKS ⟨x,by simpa only [Metric.mem_closedBall,dist_zero_right,hx] using le_rfl,rfl⟩
  obtain ⟨y,hyt,hy⟩:=mem_iUnion₂.mp (hcover hxs)
  have hyW:y∈W:=Submodule.subset_span (by simpa using hyt)
  have hmin: ‖K x-W.starProjection (K x)‖≤‖K x-y‖ := by
    rw [Submodule.starProjection_minimal]
    have hb : BddBelow (Set.range (fun z:W=>‖K x-(z:E)‖)):=⟨0,by
      rintro _ ⟨z,rfl⟩
      exact norm_nonneg _⟩
    exact ciInf_le hb ⟨y,hyW⟩
  change ‖K x-W.starProjection (K x)‖≤ε
  exact hmin.trans (le_of_lt (by simpa only [Metric.mem_ball,dist_eq_norm] using hy))

end
end Resonance.CompactOrthogonalApproximation
