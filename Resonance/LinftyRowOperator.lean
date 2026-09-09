import Resonance.ContinuousRowOperator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! True L-infinity equivalence classes act inside the integral.  The
output is continuous at every point of the compact target.  No continuity
of the input or of a representative is required. -/
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BoundedContinuousFunction
namespace Resonance.LinftyRowOperator
noncomputable section
set_option maxHeartbeats 900000
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace Y] {μ : Measure Y}

omit [TopologicalSpace X] [CompactSpace X] in
theorem ae_norm_bound (f : Lp ℝ ∞ μ) : ∀ᵐ y ∂μ, ‖f y‖ ≤ ‖f‖ := by
  simpa only [← toReal_eLpNorm (Lp.aestronglyMeasurable f),Lp.norm_def] using
    ae_le_lpNorm_exponent_top (Lp.memLp f)

def readout (K : X → Y → ℝ) (f : Lp ℝ ∞ μ) (x : X) : ℝ := ∫ y, K x y*f y ∂μ

omit [TopologicalSpace X] [CompactSpace X] in
theorem product_integrable (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (f : Lp ℝ ∞ μ) (x : X) : Integrable (fun y => K x y*f y) μ :=
  (hi x).mul_bdd (Lp.aestronglyMeasurable f) (ae_norm_bound f)

omit [TopologicalSpace X] [CompactSpace X] in
theorem readout_bound (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (f : Lp ℝ ∞ μ) (x : X) :
    ‖readout K f x‖ ≤ ‖f‖*(∫ y, ‖K x y‖ ∂μ) := by
  unfold readout
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hi x).norm.const_mul ‖f‖)
  filter_upwards [ae_norm_bound f] with y hy
  rw [norm_mul,mul_comm ‖f‖]
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)

omit [TopologicalSpace X] [CompactSpace X] in
theorem readout_difference_bound (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (f : Lp ℝ ∞ μ) (x a : X) :
    ‖readout K f a-readout K f x‖ ≤ ‖f‖*(∫ y, ‖K a y-K x y‖ ∂μ) := by
  rw [readout,readout,← integral_sub (product_integrable K hi f a) (product_integrable K hi f x)]
  have heq (y : Y) : K a y*f y-K x y*f y=(K a y-K x y)*f y := by ring
  simp_rw [heq]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (((hi a).sub (hi x)).norm.const_mul ‖f‖)
  filter_upwards [ae_norm_bound f] with y hy
  rw [norm_mul,mul_comm ‖f‖]
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)

omit [CompactSpace X] in
theorem readout_continuous (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (f : Lp ℝ ∞ μ) : Continuous (readout K f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (readout_difference_bound K hi f x)
  simpa only [mul_zero] using (tendsto_const_nhds (x := ‖f‖)).mul (hc x)

def operatorLinear (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0)) :
    Lp ℝ ∞ μ →ₗ[ℝ] C(X,ℝ) where
  toFun f := ⟨readout K f,readout_continuous K hi hc f⟩
  map_add' f g := by
    ext x
    change (∫ y, K x y*(f+g) y ∂μ)=(∫ y,K x y*f y∂μ)+(∫ y,K x y*g y∂μ)
    rw [← integral_add (product_integrable K hi f x) (product_integrable K hi g x)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    change (f+g) y=f y+g y at hy
    rw [hy,mul_add]
  map_smul' c f := by
    ext x
    change (∫ y, K x y*(c • f) y ∂μ)=c*(∫ y,K x y*f y∂μ)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with y hy
    change (c • f) y=c*f y at hy
    rw [hy]
    ring

theorem operator_bound (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, (∫ y, ‖K x y‖ ∂μ) ≤ M) (f : Lp ℝ ∞ μ) :
    ‖operatorLinear K hi hc f‖ ≤ M*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg f))).mpr
  intro x
  exact (readout_bound K hi f x).trans
    ((mul_le_mul_of_nonneg_left (hb x) (norm_nonneg f)).trans_eq (mul_comm _ _))

def operator (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, (∫ y, ‖K x y‖ ∂μ) ≤ M) :
    Lp ℝ ∞ μ →L[ℝ] C(X,ℝ) :=
  (operatorLinear K hi hc).mkContinuous M (operator_bound K hi hc hM hb)

theorem operator_compact (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, (∫ y, ‖K x y‖ ∂μ) ≤ M) :
    IsCompactOperator (operator K hi hc M hM hb) := by
  let T := operator K hi hc M hM hb
  let L := ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ
  let A : Set (X →ᵇ ℝ) := (fun f : Lp ℝ ∞ μ => L (T f)) '' closedBall 0 1
  have hnorm {f : Lp ℝ ∞ μ} (hf : f ∈ closedBall 0 1) : ‖f‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hf
  have hin : ∀ (b : X →ᵇ ℝ) (x : X), b ∈ A → b x ∈ closedBall 0 M := by
    rintro b x ⟨f,hf,rfl⟩
    rw [mem_closedBall,dist_zero_right]
    change ‖readout K f x‖ ≤ M
    apply (readout_bound K hi f x).trans
    exact (mul_le_mul (hnorm hf) (hb x) (integral_nonneg (fun _ => norm_nonneg _))
      (by norm_num)).trans_eq (one_mul M)
  have heq : Equicontinuous ((↑) : A → X → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [(tendsto_order.mp (hc x)).2 ε hε] with a ha
    rintro ⟨b, f,hf,rfl⟩
    change dist (readout K f x) (readout K f a) < ε
    rw [dist_comm,dist_eq_norm]
    apply (readout_difference_bound K hi f x a).trans_lt
    exact ((mul_le_mul_of_nonneg_right (hnorm hf)
      (integral_nonneg (fun _ => norm_nonneg _))).trans_eq (one_mul _)).trans_lt ha
  have hcompact := BoundedContinuousFunction.arzela_ascoli (closedBall (0:ℝ) M)
    (isCompact_closedBall 0 M) A hin heq
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    T.toLinearMap (by norm_num : (0:ℝ) < 1)).mpr
  refine ⟨L.symm '' closure A,hcompact.image L.symm.continuous,?_⟩
  rintro b ⟨f,hf,rfl⟩
  refine ⟨L (T f),subset_closure ?_,?_⟩
  · exact ⟨f,hf,rfl⟩
  · exact L.symm_apply_apply (T f)

theorem exists_compact_operator (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0)) :
    ∃ T : Lp ℝ ∞ μ →L[ℝ] C(X,ℝ), IsCompactOperator T ∧
      ∀ f x, T f x = ∫ y, K x y*f y ∂μ := by
  obtain ⟨M,hM,hb⟩ := ContinuousRowOperator.rowNorm_uniform_bound K hi hc
  exact ⟨operator K hi hc M hM hb,operator_compact K hi hc M hM hb,fun _ _ => rfl⟩

end
end Resonance.LinftyRowOperator
