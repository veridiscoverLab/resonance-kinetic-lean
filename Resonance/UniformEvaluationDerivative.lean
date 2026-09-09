import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact

/-! Pointwise derivatives under one continuous operator field give the actual
supremum-norm derivative.  The mean-value estimate is uniform before taking the
supremum; no exchange of a pointwise limit and a supremum is assumed. -/
open Set Filter
open scoped Topology
namespace Resonance.UniformEvaluationDerivative
noncomputable section
variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K] [CompactSpace K]

theorem eval_comp_norm_le (T : E →L[ℝ] C(K,F)) (k : K) :
    ‖(ContinuousMap.evalCLM (R := ℝ) k).comp T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (ContinuousMap.norm_coe_le_norm (T v) k).trans (T.le_opNorm v)

/-- The same derivative field controls all evaluations in the supremum norm. -/
theorem hasStrictFDerivAt_of_evaluations
    {u : E → C(K,F)} {A : E → E →L[ℝ] C(K,F)} {x : E}
    (hA : ContinuousAt A x)
    (hu : ∀ y k, HasFDerivAt (fun z => u z k)
      ((ContinuousMap.evalCLM (R := ℝ) k).comp (A y)) y) :
    HasStrictFDerivAt u (A x) x := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  apply Metric.eventually_nhds_iff_ball.mpr
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hA (Metric.ball_mem_nhds (A x) hc))
  refine ⟨ε,hε,?_⟩
  rintro ⟨a,b⟩ hab
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at hab
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).mpr
  intro k
  have hbound : ∀ y ∈ Metric.ball x ε,
      ‖(ContinuousMap.evalCLM (R := ℝ) k).comp (A y) -
        (ContinuousMap.evalCLM (R := ℝ) k).comp (A x)‖ ≤ c := by
    intro y hy
    rw [← ContinuousLinearMap.comp_sub]
    refine (eval_comp_norm_le (A y-A x) k).trans ?_
    exact (show ‖A y-A x‖<c by simpa [Metric.mem_ball, dist_eq_norm] using hball hy).le
  exact (convex_ball x ε).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun y _ => (hu y k).hasFDerivWithinAt) hbound hab.2 hab.1

theorem hasFDerivAt_of_evaluations
    {u : E → C(K,F)} {A : E → E →L[ℝ] C(K,F)} {x : E}
    (hA : ContinuousAt A x)
    (hu : ∀ y k, HasFDerivAt (fun z => u z k)
      ((ContinuousMap.evalCLM (R := ℝ) k).comp (A y)) y) :
    HasFDerivAt u (A x) x :=
  (hasStrictFDerivAt_of_evaluations hA hu).hasFDerivAt

end
end Resonance.UniformEvaluationDerivative
