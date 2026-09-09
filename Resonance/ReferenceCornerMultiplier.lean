import Resonance.CornerPairTruncation
import Resonance.ReferenceFrequencySpace

/-! Strong disappearance of the actual eight-corner multiplier in the
fixed physical Hν space. The corner set and the measure are the original
ones; no replacement marginal or pointwise lower bound for ν is used. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.ReferenceCornerMultiplier
noncomputable section
open ResonantMeasure ReferenceFrequencySpace CornerPairTruncation LpOperators
set_option maxHeartbeats 1800000

def cornerOp (R η : ℝ) : Space R →L[ℝ] Space R :=
  multiplyCLM (cut_memLp R η (referenceMeasure R))

theorem cornerOp_ae (R η : ℝ) (u : Space R) :
    cornerOp R η u =ᵐ[referenceMeasure R] (fun k=>u k*cut R η k) :=
  multiply_ae (cut_memLp R η (referenceMeasure R)) u

theorem reference_depth_positive {R : ℝ} (hR : 0 < R) :
    ∀ᵐk∂referenceMeasure R, 0 < CornerFrequencyBounds.cornerDepth R k :=
  (Measure.absolutelyContinuous_of_le_smul (reference_le_unit hR.le)).ae_le
    (depth_positive_marginal hR JointWeightComparison.unitParameter)

theorem cornerOp_bound (R η : ℝ) (u : Space R) : ‖cornerOp R η u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cornerOp_ae R η u] with k hk
  rw [hk,norm_mul]
  have hb : ‖cut R η k‖ ≤ 1 := (cut_bounds R η k).2
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_one _)

theorem cornerOp_norm (R η : ℝ) : ‖cornerOp R η‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa only [one_mul] using cornerOp_bound R η

theorem cornerOp_norm_square (R η : ℝ) (u : Space R) :
    ‖cornerOp R η u‖^2 = ∫k,(u k*cut R η k)^2∂referenceMeasure R := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cornerOp_ae R η u] with k hk
  change cornerOp R η u k*cornerOp R η u k = _
  rw [hk,pow_two]

/-- A true strong-operator limit. The norm of the corner projection is
not asserted to tend to zero. -/
theorem actual_corner_strong {R : ℝ} (hR : 0 < R) (u : Space R) :
    Tendsto (fun η:ℝ=>cornerOp R η u) (𝓝 0) (𝓝 0) := by
  have ht : Tendsto (fun η:ℝ=>∫k,(u k*cut R η k)^2∂referenceMeasure R)
      (𝓝 0) (𝓝 0) := by
    have hh:=tendsto_integral_filter_of_dominated_convergence
      (μ:=referenceMeasure R) (l:=𝓝 (0:ℝ))
      (F:=fun η k=>(u k*cut R η k)^2) (f:=fun _=>0) (fun k=>(u k)^2)
    simp only [integral_zero] at hh
    apply hh
    · exact Eventually.of_forall (fun η=>
        ((Lp.memLp u).aestronglyMeasurable.mul (cut_measurable R η).aestronglyMeasurable).pow 2)
    · apply Eventually.of_forall
      intro η
      apply ae_of_all
      intro k
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb : |u k*cut R η k| ≤ |u k| := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (cut_bounds R η k).2 (abs_nonneg _)).trans_eq (mul_one _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    · exact (Lp.memLp u).integrable_sq
    · filter_upwards [reference_depth_positive hR] with k hk
      simpa only [mul_zero,zero_pow (by norm_num:2≠0)] using
        ((tendsto_const_nhds (x:=u k)).mul (cut_tendsto hk)).pow 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he : (fun η:ℝ=>‖cornerOp R η u‖)=
      (fun η=>Real.sqrt (∫k,(u k*cut R η k)^2∂referenceMeasure R)) := by
    funext η
    rw [←cornerOp_norm_square,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  rw [he]
  simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp ht

/-- A coefficient bounded by a bulk error plus a bounded corner error is
controlled on every fixed vector by the actual corner projection. -/
theorem multiplier_envelope_bound (R η : ℝ) {b : E→ℝ}
    (hb : MemLp b ∞ (referenceMeasure R)) {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (henv : ∀ᵐk∂referenceMeasure R, |b k| ≤ κ+M*cut R η k) (u : Space R) :
    ‖multiplyCLM hb u‖ ≤ κ*‖u‖+M*‖cornerOp R η u‖ := by
  let w : Space R := κ • u+M • cornerOp R η u
  have hn : ‖multiplyCLM hb u‖ ≤ ‖w‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [multiply_ae hb u,cornerOp_ae R η u,henv,
      Lp.coeFn_add (κ • u) (M • cornerOp R η u),
      Lp.coeFn_smul κ u,Lp.coeFn_smul M (cornerOp R η u)] with k hbv hcut he ha hsu hsc
    change |multiplyCLM hb u k| ≤ |w k|
    change (κ • u+M • cornerOp R η u) k = _ at ha
    simp only [Pi.add_apply] at ha
    simp only [Pi.smul_apply,smul_eq_mul] at hsu hsc
    change multiplyCLM hb u k=u k*b k at hbv
    change |multiplyCLM hb u k| ≤ |(κ • u+M • cornerOp R η u) k|
    rw [hbv,ha,hsu,hsc,hcut]
    have hw : κ*u k+M*(u k*cut R η k)=u k*(κ+M*cut R η k) := by ring
    rw [hw,abs_mul,abs_mul,abs_of_nonneg
      (add_nonneg hκ (mul_nonneg hM (cut_bounds R η k).1))]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
  refine hn.trans ((norm_add_le _ _).trans ?_)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hκ,abs_of_nonneg hM]

/-- This needs only the actual pointwise coefficient envelope, not a
strong-convergence premise. The multiplier may keep order-one corner
values throughout. -/
theorem actual_enveloped_multiplier_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (b : I→E→ℝ) (hb : ∀i,MemLp (b i) ∞ (referenceMeasure R))
    (κ η : I→ℝ) {M : ℝ} (hM : 0 ≤ M)
    (henv : ∀i, ∀ᵐk∂referenceMeasure R, |b i k| ≤ |κ i|+M*cut R (η i) k)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (u : Space R) :
    Tendsto (fun i=>multiplyCLM (hb i) u) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := ((hκ.abs).mul_const ‖u‖).add
    ((((actual_corner_strong hR u).comp hη).norm).const_mul M)
  simp only [abs_zero,zero_mul,norm_zero,mul_zero,add_zero] at ht
  exact squeeze_zero (fun _=>norm_nonneg _)
    (fun i=>multiplier_envelope_bound R (η i) (hb i) (abs_nonneg _) hM (henv i) u) ht

end
end Resonance.ReferenceCornerMultiplier
