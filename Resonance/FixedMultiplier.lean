import Mathlib

/-!
The fixed-test multiplier bridge in the strong-current proof. The same sequence
converging in measure for μ acts on a fixed L²(σ) test, with σ ≪ μ. No convergence
of a moving microscopic vector, no marginal identity, and no coercivity estimate
is assumed to follow from this theorem.
-/
namespace Resonance.FixedMultiplier

open MeasureTheory Filter
open scoped Topology

variable {α ι E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ σ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]

theorem bounded_multiplier_sq_integrable
    {b c : α → ℝ} {V : α → E} {C : ℝ}
    (hb : AEStronglyMeasurable b σ) (hc : AEStronglyMeasurable c σ)
    (hbnd : ∀ᵐ x ∂σ, |b x| ≤ C) (hcnd : ∀ᵐ x ∂σ, |c x| ≤ C)
    (hV : MemLp V 2 σ) :
    Integrable (fun x => ‖(b x - c x) • V x‖ ^ 2) σ := by
  have hmeas : AEStronglyMeasurable (fun x => ‖(b x-c x) • V x‖ ^ 2) σ :=
    ((hb.sub hc).smul hV.aestronglyMeasurable).norm.pow 2
  apply Integrable.mono' ((hV.integrable_norm_pow (by norm_num)).const_mul ((2*C)^2)) hmeas
  filter_upwards [hbnd, hcnd] with x hbx hcx
  have hd : |b x-c x| ≤ 2*C := by
    calc
      _ ≤ |b x| + |c x| := abs_sub _ _
      _ ≤ 2*C := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, Real.norm_eq_abs, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hd 2) (sq_nonneg _)

theorem fixed_multiplier_square_tendsto
    {b : ι → α → ℝ} {c : α → ℝ} {V : α → E} {C : ℝ}
    (hac : σ ≪ μ) (hconv : TendstoInMeasure μ b l c)
    (hb : ∀ n, AEStronglyMeasurable (b n) σ) (hc : AEStronglyMeasurable c σ)
    (hbnd : ∀ n, ∀ᵐ x ∂σ, |b n x| ≤ C) (hcnd : ∀ᵐ x ∂σ, |c x| ≤ C)
    (hV : MemLp V 2 σ) :
    Tendsto (fun n => ∫ x, ‖(b n x-c x) • V x‖ ^ 2 ∂σ) l (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hlim⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hlimσ := hac.ae_le hlim
  have hbound : Integrable (fun x => (2*C)^2 * ‖V x‖^2) σ :=
    (hV.integrable_norm_pow (by norm_num)).const_mul ((2*C)^2)
  have hpoint : ∀ n, ∀ᵐ x ∂σ, ‖‖(b (ns (ms n)) x-c x) • V x‖^2‖ ≤
      (2*C)^2 * ‖V x‖^2 := by
    intro n
    filter_upwards [hbnd (ns (ms n)), hcnd] with x hbx hcx
    have hd : |b (ns (ms n)) x-c x| ≤ 2*C := by
      calc
        _ ≤ |b (ns (ms n)) x| + |c x| := abs_sub _ _
        _ ≤ 2*C := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hd 2) (sq_nonneg _)
  have hp : ∀ᵐ x ∂σ, Tendsto (fun n => ‖(b (ns (ms n)) x-c x) • V x‖^2)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlimσ] with x hx
    have hh := (((hx.sub_const (c x)).smul_const (V x)).norm).pow 2
    simpa using hh
  have ht := tendsto_integral_of_dominated_convergence (fun x => (2*C)^2 * ‖V x‖^2)
    (fun n => (((hb (ns (ms n))).sub hc).smul hV.aestronglyMeasurable).norm.pow 2)
    hbound hpoint hp
  simpa using ht

theorem fixed_multiplier_L2_tendsto
    {b : ι → α → ℝ} {c : α → ℝ} {V : α → E} {C : ℝ}
    (hac : σ ≪ μ) (hconv : TendstoInMeasure μ b l c)
    (hb : ∀ n, AEStronglyMeasurable (b n) σ) (hc : AEStronglyMeasurable c σ)
    (hbnd : ∀ n, ∀ᵐ x ∂σ, |b n x| ≤ C) (hcnd : ∀ᵐ x ∂σ, |c x| ≤ C)
    (hV : MemLp V 2 σ) :
    (∀ n, MemLp (fun x => (b n x-c x) • V x) 2 σ) ∧
    Tendsto (fun n => Real.sqrt (∫ x, ‖(b n x-c x) • V x‖ ^ 2 ∂σ)) l (𝓝 0) := by
  constructor
  · intro n
    exact (memLp_two_iff_integrable_sq_norm (((hb n).sub hc).smul hV.aestronglyMeasurable)).mpr
      (bounded_multiplier_sq_integrable (hb n) hc (hbnd n) hcnd hV)
  · have ht := fixed_multiplier_square_tendsto hac hconv hb hc hbnd hcnd hV
    simpa using (Real.continuous_sqrt.tendsto 0).comp ht


omit [NormedSpace ℝ E] in
theorem L2_norm_eq_sqrt [InnerProductSpace ℝ E] {F : α → E} (hF : MemLp F 2 σ) :
    ‖hF.toLp F‖ = Real.sqrt (∫ x, ‖F x‖^2 ∂σ) := by
  have hs : ‖hF.toLp F‖^2 = ∫ x, ‖F x‖^2 ∂σ := by
    calc
      _ = inner ℝ (hF.toLp F) (hF.toLp F) := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x, inner ℝ ((hF.toLp F) x) ((hF.toLp F) x) ∂σ := rfl
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hF.coeFn_toLp] with x hx
        rw [hx, real_inner_self_eq_norm_sq]
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Strong convergence in the actual Mathlib L² space, with a.e. representatives
and their membership proofs constructed rather than assumed. -/
theorem fixed_multiplier_strong [InnerProductSpace ℝ E]
    {b : ι → α → ℝ} {c : α → ℝ} {V : α → E} {C : ℝ}
    (hac : σ ≪ μ) (hconv : TendstoInMeasure μ b l c)
    (hb : ∀ n, AEStronglyMeasurable (b n) σ) (hc : AEStronglyMeasurable c σ)
    (hbnd : ∀ n, ∀ᵐ x ∂σ, |b n x| ≤ C) (hcnd : ∀ᵐ x ∂σ, |c x| ≤ C)
    (hV : MemLp V 2 σ) :
    ∃ F : ι → Lp E 2 σ, (∀ n, F n =ᵐ[σ] (fun x => (b n x-c x) • V x)) ∧
      Tendsto F l (𝓝 0) := by
  have hmem := (fixed_multiplier_L2_tendsto hac hconv hb hc hbnd hcnd hV).1
  let F : ι → Lp E 2 σ := fun n => (hmem n).toLp (fun x => (b n x-c x) • V x)
  refine ⟨F, fun n => (hmem n).coeFn_toLp, ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have heq : (fun n => ‖F n‖) =
      (fun n => Real.sqrt (∫ x, ‖(b n x-c x) • V x‖^2 ∂σ)) := by
    funext n
    exact L2_norm_eq_sqrt (hmem n)
  rw [heq]
  exact (fixed_multiplier_L2_tendsto hac hconv hb hc hbnd hcnd hV).2

end Resonance.FixedMultiplier
