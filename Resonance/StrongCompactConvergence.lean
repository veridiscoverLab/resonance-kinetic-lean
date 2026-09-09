import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Basic

/-! Uniformly bounded strong convergence is uniform on a fixed compact
operator image. A finite cover is constructed inside the proof. -/
open Set Metric Filter
open scoped Topology
namespace Resonance.StrongCompactConvergence
noncomputable section
variable {E F G I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
set_option maxHeartbeats 1800000

theorem compact_image_operator_norm_tendsto (K : E→L[ℝ]F) (hK : IsCompactOperator K)
    (T : I→F→L[ℝ]G) (l : Filter I) {B : ℝ} (hB : 0≤B)
    (hbound : ∀ᶠi in l,‖T i‖≤B) (hstrong : ∀x,Tendsto (fun i=>T i x) l (𝓝 0)) :
    Tendsto (fun i=>‖(T i).comp K‖) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ:=ε/(4*(B+1))
  have hδ : 0<δ:=by dsimp [δ]; positivity
  have hBd : B*δ≤ε/4 := by
    have h1: B*δ≤(B+1)*δ:=mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have he:(B+1)*δ=ε/4:=by dsimp [δ]; field_simp
    exact h1.trans_eq he
  obtain ⟨S,hS,hKS⟩:=hK.image_closedBall_subset_compact (f:=K.toLinearMap) 1
  obtain ⟨t,_,ht,hcover⟩:=hS.finite_cover_balls hδ
  letI:=ht.fintype
  have hfinite : ∀ᶠi in l,∀y:t,‖T i y‖<ε/4 := by
    apply Filter.eventually_all.mpr
    intro y
    have hy: Tendsto (fun i=>‖T i y‖) l (𝓝 0):=by simpa using (hstrong y).norm
    exact hy.eventually (gt_mem_nhds (by positivity : 0<ε/4))
  filter_upwards [hbound,hfinite] with i hi hfin
  have hop : ‖(T i).comp K‖≤ε/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have hxs:K x∈S:=hKS ⟨x,by simpa only [Metric.mem_closedBall,dist_zero_right,hx] using le_rfl,rfl⟩
    obtain ⟨y,hyt,hy⟩:=mem_iUnion₂.mp (hcover hxs)
    have hdist:‖K x-y‖≤δ:=le_of_lt (by simpa only [Metric.mem_ball,dist_eq_norm] using hy)
    have hty:‖T i y‖≤ε/4:=(hfin ⟨y,hyt⟩).le
    change ‖T i (K x)‖≤ε/2
    calc
      _=‖T i (K x-y)+T i y‖:=by rw [map_sub,sub_add_cancel]
      _≤‖T i (K x-y)‖+‖T i y‖:=norm_add_le _ _
      _≤‖T i‖*‖K x-y‖+ε/4:=add_le_add ((T i).le_opNorm _) hty
      _≤B*δ+ε/4:=add_le_add (mul_le_mul hi hdist (norm_nonneg _) hB) le_rfl
      _≤ε/2:=by linarith
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using
    (lt_of_le_of_lt hop (by linarith : ε/2<ε))

end
end Resonance.StrongCompactConvergence
