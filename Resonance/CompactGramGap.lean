import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact

/-! A proved compactness-to-coercivity step for a complete Gram operator.
The compactness premise is explicit; applying this to a collision operator
still requires a proof about that operator's actual off-diagonal kernels. -/
open Set Filter
open scoped Topology
namespace Resonance.CompactGramGap
noncomputable section
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]

theorem orthogonal_unit_gap (T : H→L[ℝ]J)
    (hcompact : IsCompactOperator (T.adjoint.comp T-1 : H→L[ℝ]H)) :
    ∃γ : ℝ,0<γ ∧ ∀v : H,v∈T.kerᗮ→‖v‖=1→γ≤‖T v‖ := by
  by_contra hn
  push Not at hn
  have hc (n : ℕ) : ∃v : H,v∈T.kerᗮ ∧ ‖v‖=1 ∧ ‖T v‖<1/((n:ℝ)+1) :=
    hn (1/((n:ℝ)+1)) (by positivity)
  choose u hu hnorm hsmall using hc
  have hTu : Tendsto (fun n=>T (u n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n=>(hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  let K : H→L[ℝ]H := T.adjoint.comp T-1
  obtain ⟨C,hC,hcover⟩ := hcompact.image_closedBall_subset_compact 1
  obtain ⟨y,_,s,hs,hconv⟩ := hC.tendsto_subseq
    (x := fun n=>K (u n)) (fun n=>hcover ⟨u n,by simp [hnorm],rfl⟩)
  have hAu : Tendsto (fun n=>T.adjoint (T (u n))) atTop (𝓝 0) := by
    simpa only [map_zero] using T.adjoint.continuous.continuousAt.tendsto.comp hTu
  have huseq : Tendsto (u∘s) atTop (𝓝 (-y)) := by
    have h := (hAu.comp hs.tendsto_atTop).sub hconv
    simpa [K,Function.comp_def] using h
  have hyorth : -y∈T.kerᗮ := T.ker.isClosed_orthogonal.mem_of_tendsto huseq
    (Eventually.of_forall (fun n=>hu (s n)))
  have hyker : -y∈T.ker := by
    change T (-y)=0
    exact tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp huseq)
      (hTu.comp hs.tendsto_atTop)
  have hyzero : -y=0 := by
    have h : -y∈T.ker⊓T.kerᗮ := ⟨hyker,hyorth⟩
    rwa [Submodule.inf_orthogonal_eq_bot] at h
  have hnlim : ‖-y‖=1 := tendsto_nhds_unique huseq.norm
    (by simp only [Function.comp_def,hnorm]; exact tendsto_const_nhds)
  simp [hyzero] at hnlim

theorem orthogonal_norm_gap (T : H→L[ℝ]J)
    (hcompact : IsCompactOperator (T.adjoint.comp T-1 : H→L[ℝ]H)) :
    ∃γ : ℝ,0<γ ∧ ∀v : H,v∈T.kerᗮ→γ*‖v‖≤‖T v‖ := by
  obtain ⟨γ,hγ,hunit⟩ := orthogonal_unit_gap T hcompact
  refine ⟨γ,hγ,?_⟩
  intro v hv
  by_cases hz : v=0
  · simp [hz]
  have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hz
  have hnorm : ‖(‖v‖⁻¹ : ℝ) • v‖=1 := by simp [norm_smul,hn]
  have h := hunit ((‖v‖⁻¹ : ℝ) • v) (T.kerᗮ.smul_mem _ hv) hnorm
  have hr : ‖v‖ • ((‖v‖⁻¹ : ℝ) • v)=v := by simp [smul_smul,hn]
  calc
    γ*‖v‖=‖v‖*γ := mul_comm _ _
    _ ≤ ‖v‖*‖T ((‖v‖⁻¹ : ℝ) • v)‖ := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖(‖v‖ : ℝ) • T ((‖v‖⁻¹ : ℝ) • v)‖ := by rw [norm_smul,norm_norm]
    _ = ‖T (‖v‖ • ((‖v‖⁻¹ : ℝ) • v))‖ := by simp only [map_smul]
    _ = ‖T v‖ := by rw [hr]

theorem projected_square_gap (T : H→L[ℝ]J)
    (hcompact : IsCompactOperator (T.adjoint.comp T-1 : H→L[ℝ]H)) :
    ∃δ : ℝ,0<δ ∧ ∀v : H,δ*‖v-T.ker.starProjection v‖^2≤‖T v‖^2 := by
  obtain ⟨γ,hγ,hgap⟩ := orthogonal_norm_gap T hcompact
  refine ⟨γ^2,by positivity,?_⟩
  intro v
  have h := hgap (v-T.ker.starProjection v) (T.ker.sub_starProjection_mem_orthogonal v)
  have hnull : T (T.ker.starProjection v)=0 := T.ker.starProjection_apply_mem v
  rw [map_sub,hnull,sub_zero] at h
  have hsq := pow_le_pow_left₀ (mul_nonneg hγ.le (norm_nonneg _)) h 2
  simpa only [mul_pow] using hsq

end
end Resonance.CompactGramGap
