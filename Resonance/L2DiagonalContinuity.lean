import Resonance.L2DiagonalOperator
import Mathlib.Analysis.Normed.Group.Tannery

/-! Strong continuity on the full completed coefficient space, proved by
summable domination of the common squared difference. -/
open ContinuousLinearMap Filter
open scoped Topology NNReal
namespace Resonance.L2DiagonalContinuity
noncomputable section
open L2DiagonalOperator
variable {I E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace P]

theorem diagonal_strong_continuous (T : P→I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C)
    (hT : ∀t i,‖T t i‖≤C) (hcont : ∀i v,Continuous (fun t=>T t i v))
    (v : Space I E) : Continuous (fun t=>diagonal (T t) hC (hT t) v) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hs : Summable (fun i=>4*C^2*‖v i‖^2) :=
    (hasSum_norm_square v).summable.mul_left (4*C^2)
  have hc : ∀i,Tendsto (fun t=>‖T t i (v i)-T t₀ i (v i)‖^2) (𝓝 t₀) (𝓝 (0:ℝ)) := by
    intro i
    simpa using (((hcont i (v i)).sub (continuous_const (y:=T t₀ i (v i)))).norm.pow 2).tendsto t₀
  have hb : ∀t i,‖‖T t i (v i)-T t₀ i (v i)‖^2‖≤4*C^2*‖v i‖^2 := by
    intro t i
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖T t i (v i)‖≤C*‖v i‖ :=
      (T t i).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hT t i) (norm_nonneg _))
    have h2 : ‖T t₀ i (v i)‖≤C*‖v i‖ :=
      (T t₀ i).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hT t₀ i) (norm_nonneg _))
    have hh : ‖T t i (v i)-T t₀ i (v i)‖≤2*C*‖v i‖ := by
      linarith [norm_sub_le (T t i (v i)) (T t₀ i (v i))]
    have hsq := (sq_le_sq₀ (norm_nonneg _) (show 0≤2*C*‖v i‖ by positivity)).mpr hh
    nlinarith
  have ht := tendsto_tsum_of_dominated_convergence hs hc (Eventually.of_forall hb)
  have hsq : Tendsto (fun t=>‖diagonal (T t) hC (hT t) v-
      diagonal (T t₀) hC (hT t₀) v‖^2) (𝓝 t₀) (𝓝 (0:ℝ)) := by
    simpa only [←(hasSum_norm_square _).tsum_eq,lp.coeFn_sub,Pi.sub_apply,
      diagonal_apply,tsum_zero] using ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

end
end Resonance.L2DiagonalContinuity
