import Resonance.UniformEvaluationDerivative
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The uniform evaluation bridge on a convex time window. It keeps the
relative endpoint derivative and does not demand an extension of the solution
outside its actual interval. -/
open Set Filter
open scoped Topology
namespace Resonance.WithinEvaluationDerivative
noncomputable section
variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K] [CompactSpace K]

theorem hasFDerivWithinAt_of_evaluations
    {u : E → C(K,F)} {A : E → E →L[ℝ] C(K,F)} {s : Set E} {x : E}
    (hs : Convex ℝ s) (hx : x∈s) (hA : ContinuousWithinAt A s x)
    (hu : ∀ y∈s,∀ k,HasFDerivWithinAt (fun z => u z k)
      ((ContinuousMap.evalCLM (R := ℝ) k).comp (A y)) s y) :
    HasFDerivWithinAt u (A x) s x := by
  rw [hasFDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhdsWithin_iff.mp (hA (Metric.ball_mem_nhds (A x) hc))
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨ε,hε,?_⟩
  intro y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).mpr
  intro k
  have hbound : ∀ z∈Metric.ball x ε∩s,
      ‖(ContinuousMap.evalCLM (R := ℝ) k).comp (A z)-
        (ContinuousMap.evalCLM (R := ℝ) k).comp (A x)‖≤c := by
    intro z hz
    rw [←ContinuousLinearMap.comp_sub]
    refine (UniformEvaluationDerivative.eval_comp_norm_le (A z-A x) k).trans ?_
    exact (show ‖A z-A x‖<c by simpa [Metric.mem_ball,dist_eq_norm] using hball hz).le
  exact ((convex_ball x ε).inter hs).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hu z hz.2 k).mono inter_subset_right) hbound
    ⟨Metric.mem_ball_self hε,hx⟩ hy

theorem hasDerivWithinAt_of_evaluations
    {u v : ℝ→C(K,F)} {s : Set ℝ} {x : ℝ}
    (hs : Convex ℝ s) (hx : x∈s) (hv : ContinuousWithinAt v s x)
    (hu : ∀ y∈s,∀ k,HasDerivWithinAt (fun z => u z k) (v y k) s y) :
    HasDerivWithinAt u (v x) s x := by
  let A : ℝ→ℝ→L[ℝ]C(K,F) := fun t => ContinuousLinearMap.toSpanSingleton ℝ (v t)
  have hA : ContinuousWithinAt A s x := by
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ (C(K,F)) (1 : ℝ→L[ℝ]ℝ)).continuous.continuousAt).comp_continuousWithinAt hv
  exact hasFDerivWithinAt_of_evaluations hs hx hA (fun y hy k => hu y hy k)

#check hasFDerivWithinAt_of_evaluations
#check hasDerivWithinAt_of_evaluations
#print axioms hasFDerivWithinAt_of_evaluations
#print axioms hasDerivWithinAt_of_evaluations

end
end Resonance.WithinEvaluationDerivative
