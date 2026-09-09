import Resonance.CrossPairCompact
import Resonance.CornerNewtonTail
import Resonance.LpOperators
import Resonance.FixedMultiplier

/-! The two actual conditional pair operators truncated to the same
eight-corner layer. Their small norm is proved from the actual full kernels
and the actual zero-volume corner set, not assumed as a localization input. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CornerPairTruncation
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm FrequencyGramDecomposition
open ActualPairKernels ActualCrossPairing CornerNewtonTail CornerFrequencyBounds
open CornerInverseFrequency CornerLayerVolume LpOperators
set_option maxHeartbeats 1500000

def cut (R η : ℝ) (k : E) : ℝ := (fullTail R η).indicator (fun _=>1) k

theorem cut_measurable (R η : ℝ) : Measurable (cut R η) :=
  measurable_const.indicator (fullTail_measurable R η)

theorem cut_bounds (R η : ℝ) (k : E) : 0≤cut R η k ∧ |cut R η k|≤1 := by
  by_cases hk:k∈fullTail R η <;> simp [cut,hk]

theorem cut_memLp (R η : ℝ) (μ : Measure E) : MemLp (cut R η) ∞ μ := by
  apply memLp_top_of_bound (cut_measurable R η).aestronglyMeasurable 1
  exact ae_of_all _ (fun k=>by simpa only [Real.norm_eq_abs] using (cut_bounds R η k).2)

def cutOp (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ) : H R θ→L[ℝ]H R θ :=
  multiplyCLM (cut_memLp R η (marginal R θ))

theorem cutOp_ae (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ) (u : H R θ) :
    cutOp R θ η u=ᵐ[marginal R θ] (fun k=>u k*cut R η k) :=
  multiply_ae (cut_memLp R η (marginal R θ)) u

theorem cutOp_selfadjoint_pairing (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ)
    (u v : H R θ) : inner ℝ v (cutOp R θ η u)=inner ℝ (cutOp R θ η v) u := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutOp_ae R θ η u,cutOp_ae R θ η v] with k hu hv
  change cutOp R θ η u k*v k=u k*cutOp R θ η v k
  rw [hu,hv]
  ring

theorem depth_positive_marginal {R : ℝ} (hR : 0<R) (θ : Thermodynamics.Parameter) :
    ∀ᵐk∂marginal R θ,0<cornerDepth R k := by
  have hz : (volume.restrict (cube R)) {k:E|cornerDepth R k=0}=0 := by
    rw [Measure.restrict_apply
      (measurableSet_eq_fun (cornerDepth_continuous R).measurable measurable_const)]
    rw [show {k:E|cornerDepth R k=0}∩cube R={k∈cube R|cornerDepth R k=0} by
      ext k; exact and_comm]
    exact cornerDepth_zero_volume hR
  have hn : ∀ᵐk∂volume.restrict (cube R),cornerDepth R k≠0 := by
    simpa only [ae_iff,not_not] using hz
  apply (marginal_absolutelyContinuous_cube R θ 0).ae_le
  filter_upwards [hn,ae_restrict_mem (measurable_cube R)] with k hn hk
  exact lt_of_le_of_ne (cornerDepth_nonnegative hR hk) (Ne.symm hn)

theorem cut_tendsto {R : ℝ} {k : E} (hk : 0<cornerDepth R k) :
    Tendsto (fun η:ℝ=>cut R η k) (𝓝 0) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Iio_mem_nhds hk] with η hη
  have hn : k∉fullTail R η:=fun h=>not_le_of_gt hη h.2
  simp [cut,hn]

def cutKernel (R η : ℝ) (K : E×E→ℝ) (p : E×E) : ℝ :=
  K p*(cut R η p.1*cut R η p.2)

theorem cutKernel_memLp (R η : ℝ) (μ : Measure E) {K : E×E→ℝ}
    (hK : MemLp K 2 (μ.prod μ)) : MemLp (cutKernel R η K) 2 (μ.prod μ) := by
  have hm : MemLp (fun p:E×E=>cut R η p.1*cut R η p.2) ∞ (μ.prod μ) := by
    apply memLp_top_of_bound
      (((cut_measurable R η).comp measurable_fst).mul
        ((cut_measurable R η).comp measurable_snd)).aestronglyMeasurable 1
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (cut_bounds R η p.1).2 (cut_bounds R η p.2).2
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact hm.mul' hK

theorem cutKernel_square_integral_tendsto {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (_hθ : θ∈Thermodynamics.positiveDomain R)
    {K : E×E→ℝ} (hK : MemLp K 2 ((marginal R θ).prod (marginal R θ))) :
    Tendsto (fun η:ℝ=>∫p,(cutKernel R η K p)^2∂(marginal R θ).prod (marginal R θ))
      (𝓝 0) (𝓝 0) := by
  letI:=jointMeasure_finite hR.le _hθ
  letI : IsFiniteMeasure (marginal R θ):=inferInstanceAs
    (IsFiniteMeasure ((jointMeasure R θ).map (fun q=>q 0)))
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ:=(marginal R θ).prod (marginal R θ)) (l:=𝓝 (0:ℝ))
    (F:=fun η p=>(cutKernel R η K p)^2) (f:=fun _=>0) (fun p=>(K p)^2)
  simp only [integral_zero] at ht
  apply ht
  · exact Eventually.of_forall (fun η=>(cutKernel_memLp R η _ hK).aestronglyMeasurable.pow 2)
  · apply Eventually.of_forall
    intro η
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hb : |cut R η p.1*cut R η p.2|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul (cut_bounds R η p.1).2 (cut_bounds R η p.2).2
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hc : |cutKernel R η K p|≤|K p| := by
      rw [cutKernel,abs_mul]
      exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_one _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hc 2
  · exact hK.integrable_sq
  · filter_upwards [
      (Measure.quasiMeasurePreserving_fst (μ:=marginal R θ) (ν:=marginal R θ)).ae
        (depth_positive_marginal hR θ),
      (Measure.quasiMeasurePreserving_snd (μ:=marginal R θ) (ν:=marginal R θ)).ae
        (depth_positive_marginal hR θ)] with p hp1 hp2
    have hc:=((tendsto_const_nhds (x:=K p)).mul ((cut_tendsto hp1).mul (cut_tendsto hp2))).pow 2
    simpa only [mul_zero,zero_mul,zero_pow (by norm_num:2≠0),cutKernel] using hc

def pairKernel (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) : E×E→ℝ :=
  if b then kernel01 R θ else kernel02 R θ
def pairOperator (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) : H R θ→L[ℝ]H R θ :=
  if b then cross R θ 0 1 else cross R θ 0 2

theorem pairKernel_memLp {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) :
    MemLp (pairKernel R θ b) 2 ((marginal R θ).prod (marginal R θ)) := by
  cases b
  · exact CrossPairCompact.cross_kernel_memLp hR hθ
  · exact IncomingPairCompact.incoming_kernel_memLp hR hθ

theorem pairOperator_represents {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (u v : H R θ) :
    inner ℝ v (pairOperator R θ b u)=
      ∫p,pairKernel R θ b p*u p.2*v p.1∂(marginal R θ).prod (marginal R θ) := by
  cases b
  · exact kernel02_represents hR hθ v u
  · exact kernel01_represents hR hθ v u

def cutPair (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) (η : ℝ) : H R θ→L[ℝ]H R θ :=
  (cutOp R θ η).comp ((pairOperator R θ b).comp (cutOp R θ η))

theorem cutPair_represents {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (η : ℝ) :
    L2KernelPairing.Represents (marginal R θ) (marginal R θ)
      ((cutKernel_memLp R η _ (pairKernel_memLp hR hθ b)).toLp
        (cutKernel R η (pairKernel R θ b))) (cutPair R θ b η) := by
  letI:=jointMeasure_finite hR.le hθ
  letI : IsFiniteMeasure (marginal R θ):=inferInstanceAs
    (IsFiniteMeasure ((jointMeasure R θ).map (fun q=>q 0)))
  intro u v
  change inner ℝ v (cutOp R θ η (pairOperator R θ b (cutOp R θ η u)))=_
  rw [cutOp_selfadjoint_pairing,pairOperator_represents hR hθ]
  apply integral_congr_ae
  filter_upwards [
    (Measure.quasiMeasurePreserving_fst (μ:=marginal R θ) (ν:=marginal R θ)).ae_eq
      (cutOp_ae R θ η v),
    (Measure.quasiMeasurePreserving_snd (μ:=marginal R θ) (ν:=marginal R θ)).ae_eq
      (cutOp_ae R θ η u),
    (cutKernel_memLp R η _ (pairKernel_memLp hR hθ b)).coeFn_toLp] with p hv hu hK
  simp only [Function.comp_def] at hu hv
  rw [hu,hv,hK]
  unfold cutKernel
  ring

theorem cutPair_norm_le {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (η : ℝ) :
    ‖cutPair R θ b η‖≤Real.sqrt
      (∫p,(cutKernel R η (pairKernel R θ b) p)^2∂(marginal R θ).prod (marginal R θ)) := by
  letI:=jointMeasure_finite hR.le hθ
  letI : IsFiniteMeasure (marginal R θ):=inferInstanceAs
    (IsFiniteMeasure ((jointMeasure R θ).map (fun q=>q 0)))
  have hn:=L2KernelPairing.represents_norm_bound (marginal R θ) (marginal R θ)
    (cutPair_represents hR hθ b η)
  rw [FixedMultiplier.L2_norm_eq_sqrt] at hn
  simpa only [Real.norm_eq_abs,sq_abs] using hn

/-- The original two conditional pair operators have vanishing norm after
both legs are confined to the same actual corner layer. The input variable
η tends to zero directly, rather than only along a selected subsequence. -/
theorem actual_cutPair_norm_tendsto {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) :
    Tendsto (fun η:ℝ=>‖cutPair R θ b η‖) (𝓝 0) (𝓝 0) := by
  have ht:= (Real.continuous_sqrt.tendsto 0).comp
    (cutKernel_square_integral_tendsto hR hθ (pairKernel_memLp hR hθ b))
  simp only [Real.sqrt_zero] at ht
  exact squeeze_zero (fun _=>norm_nonneg _) (cutPair_norm_le hR hθ b) ht

def cutCross (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4) (η : ℝ) : H R θ→L[ℝ]H R θ :=
  (cutOp R θ η).comp ((cross R θ i j).comp (cutOp R θ η))

/-- All twelve distinct ordered pairs, not only a selected incoming pair,
are the two actual kernels through full-quartet relabelling. -/
theorem actual_distinct_pair_choice (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j : Fin 4) (hij : i≠j) :
    cross R θ i j=pairOperator R θ true ∨ cross R θ i j=pairOperator R θ false := by
  obtain ⟨h10,h23,h32,h03,h12,h13,h20,h21,h30,h31⟩:=cross_relations R θ
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr h03
  · exact Or.inl h10
  · exact (hij rfl).elim
  · exact Or.inr h12
  · exact Or.inr h13
  · exact Or.inr h20
  · exact Or.inr h21
  · exact (hij rfl).elim
  · exact Or.inl h23
  · exact Or.inr h30
  · exact Or.inr h31
  · exact Or.inl h32
  · exact (hij rfl).elim

theorem actual_all_distinct_cutCross_tendsto {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R)
    (i j : Fin 4) (hij : i≠j) :
    Tendsto (fun η:ℝ=>‖cutCross R θ i j η‖) (𝓝 0) (𝓝 0) := by
  rcases actual_distinct_pair_choice R θ i j hij with he|he
  · simpa only [cutCross,he,cutPair] using actual_cutPair_norm_tendsto hR hθ true
  · simpa only [cutCross,he,cutPair] using actual_cutPair_norm_tendsto hR hθ false

/-- One modulus for all distinct ordered legs of this same measure. -/
def omega (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ) : ℝ :=
  ‖cutPair R θ true η‖+‖cutPair R θ false η‖

theorem omega_nonnegative (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ) :
    0≤omega R θ η := add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem omega_tendsto {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    Tendsto (omega R θ) (𝓝 0) (𝓝 0) := by
  simpa only [omega,add_zero] using
    (actual_cutPair_norm_tendsto hR hθ true).add
      (actual_cutPair_norm_tendsto hR hθ false)

theorem cutCross_norm_le_omega (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j : Fin 4) (hij : i≠j) (η : ℝ) : ‖cutCross R θ i j η‖≤omega R θ η := by
  rcases actual_distinct_pair_choice R θ i j hij with he|he
  · simp only [cutCross,he,omega,cutPair]
    exact le_add_of_nonneg_right (norm_nonneg _)
  · simp only [cutCross,he,omega,cutPair]
    exact le_add_of_nonneg_left (norm_nonneg _)

theorem cut_joint_product_integrable (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j : Fin 4) (η : ℝ) (u v : H R θ) :
    Integrable (fun q:FourMomenta=>(u (q i)*cut R η (q i))*(v (q j)*cut R η (q j)))
      (jointMeasure R θ) := by
  apply ((Lp.memLp (pullback R θ i (cutOp R θ η u))).integrable_mul
    (Lp.memLp (pullback R θ j (cutOp R θ η v)))).congr
  filter_upwards [pullback_ae R θ i (cutOp R θ η u),
    pullback_ae R θ j (cutOp R θ η v),
    (all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq (cutOp_ae R θ η u),
    (all_legs_preserve R θ j).quasiMeasurePreserving.ae_eq (cutOp_ae R θ η v)]
    with q hui hvj hui' hvj'
  change pullback R θ i (cutOp R θ η u) q*pullback R θ j (cutOp R θ η v) q=_
  simp only [Function.comp_def] at hui' hvj'
  rw [hui,hvj,hui',hvj']

theorem cutCross_joint_integral (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j : Fin 4) (η : ℝ) (u v : H R θ) :
    inner ℝ u (cutCross R θ i j η v)=
      ∫q,(u (q i)*cut R η (q i))*(v (q j)*cut R η (q j))∂jointMeasure R θ := by
  change inner ℝ u (cutOp R θ η (cross R θ i j (cutOp R θ η v)))=_
  rw [cutOp_selfadjoint_pairing,cross_pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pullback_ae R θ i (cutOp R θ η u),
    pullback_ae R θ j (cutOp R θ η v),
    (all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq (cutOp_ae R θ η u),
    (all_legs_preserve R θ j).quasiMeasurePreserving.ae_eq (cutOp_ae R θ η v)]
    with q hui hvj hui' hvj'
  change pullback R θ j (cutOp R θ η v) q*pullback R θ i (cutOp R θ η u) q=_
  simp only [Function.comp_def] at hui' hvj'
  rw [hui,hvj,hui',hvj',mul_comm]

/-- The actual full-quartet bilinear estimate used by corner localization.
No independence of the two legs is introduced. -/
theorem actual_distinct_corner_pair_bound (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j : Fin 4) (hij : i≠j) (η : ℝ) (u v : H R θ) :
    |∫q,(u (q i)*cut R η (q i))*(v (q j)*cut R η (q j))∂jointMeasure R θ|
      ≤omega R θ η*‖u‖*‖v‖ := by
  rw [←cutCross_joint_integral]
  calc
    |inner ℝ u (cutCross R θ i j η v)|≤‖u‖*‖cutCross R θ i j η v‖ :=
      abs_real_inner_le_norm _ _
    _ ≤‖u‖*(‖cutCross R θ i j η‖*‖v‖) :=
      mul_le_mul_of_nonneg_left ((cutCross R θ i j η).le_opNorm v) (norm_nonneg _)
    _ ≤‖u‖*(omega R θ η*‖v‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (cutCross_norm_le_omega R θ i j hij η) (norm_nonneg _))
        (norm_nonneg _)
    _ =omega R θ η*‖u‖*‖v‖ := by ring

end
end Resonance.CornerPairTruncation
