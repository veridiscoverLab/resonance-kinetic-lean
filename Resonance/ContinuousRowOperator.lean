import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A genuine integral operator from continuous functions to continuous
functions.  Its explicit L1 rows supply the modulus on the whole unit
ball; Arzela--Ascoli proves compactness.  The cube application must prove
the row hypotheses for its original kernels. -/
open MeasureTheory Set Filter Real Metric
open scoped Topology BoundedContinuousFunction
namespace Resonance.ContinuousRowOperator
noncomputable section
set_option maxHeartbeats 900000
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure Y}

def readout (K : X → Y → ℝ) (f : C(Y,ℝ)) (x : X) : ℝ := ∫ y, K x y*f y ∂μ

omit [TopologicalSpace X] [CompactSpace X] in
theorem product_integrable (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (f : C(Y,ℝ)) (x : X) : Integrable (fun y => K x y*f y) μ :=
  (hi x).mul_bdd f.continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (fun y => f.norm_coe_le_norm y))

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace Y] in
theorem readout_bound (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (f : C(Y,ℝ)) (x : X) :
    ‖readout (μ := μ) K f x‖ ≤ ‖f‖*(∫ y, ‖K x y‖ ∂μ) := by
  unfold readout
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((hi x).norm.const_mul ‖f‖)
  filter_upwards [] with y
  rw [norm_mul,mul_comm ‖f‖]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)

omit [TopologicalSpace X] [CompactSpace X] in
theorem readout_difference_bound (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (f : C(Y,ℝ)) (x a : X) :
    ‖readout (μ := μ) K f a-readout (μ := μ) K f x‖ ≤
      ‖f‖*(∫ y, ‖K a y-K x y‖ ∂μ) := by
  rw [readout,readout,← integral_sub (product_integrable K hi f a) (product_integrable K hi f x)]
  have hpoint (y : Y) : K a y*f y-K x y*f y=(K a y-K x y)*f y := by ring
  simp_rw [hpoint]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (((hi a).sub (hi x)).norm.const_mul ‖f‖)
  filter_upwards [] with y
  rw [norm_mul,mul_comm ‖f‖]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)

omit [CompactSpace X] in
theorem readout_continuous (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (f : C(Y,ℝ)) : Continuous (readout (μ := μ) K f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (readout_difference_bound K hi f x)
  simpa only [mul_zero] using (tendsto_const_nhds (x := ‖f‖)).mul (hc x)

def operatorLinear (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0)) :
    C(Y,ℝ) →ₗ[ℝ] C(X,ℝ) where
  toFun f := ⟨readout (μ := μ) K f,readout_continuous K hi hc f⟩
  map_add' f g := by
    ext x
    change (∫ y, K x y*(f y+g y) ∂μ) = (∫ y,K x y*f y∂μ)+(∫ y,K x y*g y∂μ)
    simp_rw [mul_add]
    exact integral_add (product_integrable K hi f x) (product_integrable K hi g x)
  map_smul' c f := by
    ext x
    change (∫ y, K x y*(c*f y) ∂μ)=c*(∫ y,K x y*f y∂μ)
    have hpoint (y : Y) : K x y*(c*f y)=c*(K x y*f y) := by ring
    simp_rw [hpoint]
    exact integral_const_mul _ _

theorem operator_bound (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, (∫ y, ‖K x y‖ ∂μ) ≤ M) (f : C(Y,ℝ)) :
    ‖operatorLinear K hi hc f‖ ≤ M*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg f))).mpr
  intro x
  exact (readout_bound K hi f x).trans
    ((mul_le_mul_of_nonneg_left (hb x) (norm_nonneg f)).trans_eq (mul_comm _ _))

def operator (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, (∫ y, ‖K x y‖ ∂μ) ≤ M) :
    C(Y,ℝ) →L[ℝ] C(X,ℝ) :=
  (operatorLinear K hi hc).mkContinuous M (operator_bound K hi hc hM hb)

theorem operator_compact (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, (∫ y, ‖K x y‖ ∂μ) ≤ M) :
    IsCompactOperator (operator K hi hc M hM hb) := by
  let T := operator K hi hc M hM hb
  let L := ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ
  let A : Set (X →ᵇ ℝ) := (fun f : C(Y,ℝ) => L (T f)) '' closedBall 0 1
  have hnorm {f : C(Y,ℝ)} (hf : f ∈ closedBall 0 1) : ‖f‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hf
  have hin : ∀ (b : X →ᵇ ℝ) (x : X), b ∈ A → b x ∈ closedBall 0 M := by
    rintro b x ⟨f,hf,rfl⟩
    rw [mem_closedBall,dist_zero_right]
    change ‖readout (μ := μ) K f x‖ ≤ M
    apply (readout_bound K hi f x).trans
    exact (mul_le_mul (hnorm hf) (hb x) (integral_nonneg (fun _ => norm_nonneg _))
      (by norm_num)).trans_eq (one_mul M)
  have heq : Equicontinuous ((↑) : A → X → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [(tendsto_order.mp (hc x)).2 ε hε] with a ha
    rintro ⟨b, f,hf,rfl⟩
    change dist (readout (μ := μ) K f x) (readout (μ := μ) K f a) < ε
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

omit [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] [BorelSpace Y] in
theorem rowNorm_continuous (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0)) :
    Continuous (fun x => ∫ y, ‖K x y‖ ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ (hc x)
  intro a
  rw [← integral_sub (hi a).norm (hi x).norm]
  apply norm_integral_le_of_norm_le ((hi a).sub (hi x)).norm
  filter_upwards [] with y
  rw [Real.norm_eq_abs]
  exact abs_norm_sub_norm_le (K a y) (K x y)

omit [TopologicalSpace Y] [CompactSpace Y] [BorelSpace Y] in
theorem rowNorm_uniform_bound (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, (∫ y, ‖K x y‖ ∂μ) ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_univ.image (rowNorm_continuous K hi hc)).bddAbove
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x
  exact (hM ⟨x,mem_univ x,rfl⟩).trans (le_max_left _ _)

/-- Existence with the exact integral readout; the uniform bound is derived,
not an additional assumption on the rows. -/
theorem exists_compact_operator (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0)) :
    ∃ T : C(Y,ℝ) →L[ℝ] C(X,ℝ), IsCompactOperator T ∧
      ∀ f x, T f x = ∫ y, K x y*f y ∂μ := by
  obtain ⟨M,hM,hb⟩ := rowNorm_uniform_bound K hi hc
  exact ⟨operator K hi hc M hM hb,operator_compact K hi hc M hM hb,fun _ _ => rfl⟩

end
end Resonance.ContinuousRowOperator
