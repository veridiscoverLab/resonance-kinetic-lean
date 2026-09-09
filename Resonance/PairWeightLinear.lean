import Resonance.QuartetWeightSpace

/-! Linear dependence of a complete flagged pair average on its continuous
four-leg weight. The only row estimates used here are for the unit weight;
the actual sphere/plane instances are supplied separately. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.PairWeightLinear
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure ActualPairNormalization QuartetWeightSpace
open LinftyMultiplication (X)
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
  (R : ℝ) (Q : (E×E)×Y→FourMomenta) (hQ : Measurable Q)
  (α : E×E→ℝ) (hα : Measurable α) (hα0 : ∀p,0≤α p)

def fiber (W : WeightSpace R) (p : E×E) : ℝ := ∫y,rawWeight R W (Q (p,y))∂μ

include hQ in
theorem fiber_integrable (W : WeightSpace R) (p : E×E) :
    Integrable (fun y=>rawWeight R W (Q (p,y))) μ := by
  apply (integrable_const ‖W‖).mono'
    ((rawWeight_measurable R W).comp (hQ.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  exact ae_of_all _ (fun y=>rawWeight_norm_bound R W _)

include hQ in
theorem fiber_measurable (W : WeightSpace R) : Measurable (fiber μ R Q W) :=
  (((rawWeight_measurable R W).comp hQ).stronglyMeasurable.integral_prod_right').measurable

omit [IsFiniteMeasure μ] in
theorem fiber_one_nonnegative (p : E×E) : 0≤fiber μ R Q 1 p :=
  integral_nonneg (fun _=>rawWeight_one_nonnegative R _)

include hQ in
theorem fiber_bound (W : WeightSpace R) (p : E×E) :
    ‖fiber μ R Q W p‖≤‖W‖*fiber μ R Q 1 p := by
  unfold fiber
  rw [←integral_const_mul]
  apply norm_integral_le_of_norm_le ((fiber_integrable μ R Q hQ 1 p).const_mul ‖W‖)
  exact ae_of_all _ (fun y=>rawWeight_bound R W _)

include hQ in
theorem fiber_add (V W : WeightSpace R) (p : E×E) :
    fiber μ R Q (V+W) p=fiber μ R Q V p+fiber μ R Q W p := by
  unfold fiber
  simp_rw [rawWeight_add]
  exact integral_add (fiber_integrable μ R Q hQ V p) (fiber_integrable μ R Q hQ W p)

omit [IsFiniteMeasure μ] in
theorem fiber_smul (c : ℝ) (W : WeightSpace R) (p : E×E) :
    fiber μ R Q (c • W) p=c*fiber μ R Q W p := by
  unfold fiber
  simp_rw [rawWeight_smul]
  exact integral_const_mul c _

def kernel (W : WeightSpace R) (k p : E) : ℝ := α (k,p)*fiber μ R Q W (k,p)

include hQ hα in
theorem kernel_measurable (W : WeightSpace R) :
    Measurable (fun p : E×E=>kernel μ R Q α W p.1 p.2) :=
  hα.mul (fiber_measurable μ R Q hQ W)

include hα0 in
omit [IsFiniteMeasure μ] in
theorem kernel_one_nonnegative (k p : E) : 0≤kernel μ R Q α 1 k p :=
  mul_nonneg (hα0 _) (fiber_one_nonnegative μ R Q _)

include hQ hα0 in
theorem kernel_bound (W : WeightSpace R) (k p : E) :
    ‖kernel μ R Q α W k p‖≤‖W‖*kernel μ R Q α 1 k p := by
  unfold kernel
  rw [norm_mul,Real.norm_of_nonneg (hα0 _)]
  exact (mul_le_mul_of_nonneg_left (fiber_bound μ R Q hQ W _) (hα0 _)).trans_eq (by ring)

variable (hi : ∀k∈cube R,Integrable (kernel μ R Q α 1 k) (cubeVolume R))
  (B : ℝ) (hB : 0≤B)
  (hb : ∀k∈cube R,(∫p,kernel μ R Q α 1 k p∂cubeVolume R)≤B)

include hQ hα hα0 hi in
theorem kernel_integrable (W : WeightSpace R) {k : E} (hk : k∈cube R) :
    Integrable (kernel μ R Q α W k) (cubeVolume R) := by
  apply ((hi k hk).const_mul ‖W‖).mono'
    ((kernel_measurable μ R Q hQ α hα W).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact ae_of_all _ (fun p=>kernel_bound μ R Q hQ α hα0 W k p)

def readout (W : WeightSpace R) (f : X R) (k : E) : ℝ :=
  ∫p,kernel μ R Q α W k p*f p∂cubeVolume R

include hQ hα hα0 hi in
theorem product_integrable (W : WeightSpace R) (f : X R) {k : E} (hk : k∈cube R) :
    Integrable (fun p=>kernel μ R Q α W k p*f p) (cubeVolume R) :=
  (kernel_integrable μ R Q hQ α hα hα0 hi W hk).mul_bdd
    (Lp.aestronglyMeasurable f) (LinftyRowOperator.ae_norm_bound f)

include hQ hα in
theorem readout_measurable (W : WeightSpace R) (f : X R) :
    Measurable (readout μ R Q α W f) := by
  letI := cubeVolume_finite R
  exact (((kernel_measurable μ R Q hQ α hα W).mul
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right').measurable

include hQ hα0 hi hb in
theorem readout_bound (W : WeightSpace R) (f : X R) {k : E} (hk : k∈cube R) :
    ‖readout μ R Q α W f k‖≤(B*‖W‖)*‖f‖ := by
  have hn : ‖readout μ R Q α W f k‖≤
      ‖f‖*‖W‖*(∫p,kernel μ R Q α 1 k p∂cubeVolume R) := by
    unfold readout
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le ((hi k hk).const_mul (‖f‖*‖W‖))
    filter_upwards [LinftyRowOperator.ae_norm_bound f] with p hp
    rw [norm_mul]
    exact (mul_le_mul (kernel_bound μ R Q hQ α hα0 W k p) hp (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (kernel_one_nonnegative μ R Q α hα0 k p))).trans_eq (by ring)
  exact hn.trans ((mul_le_mul_of_nonneg_left (hb k hk) (by positivity)).trans_eq (by ring))

def readout_memLp (W : WeightSpace R) (f : X R) : MemLp (readout μ R Q α W f) ∞ (cubeVolume R) := by
  apply memLp_top_of_bound (readout_measurable μ R Q hQ α hα W f).aestronglyMeasurable
    ((B*‖W‖)*‖f‖)
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  exact readout_bound μ R Q hQ α hα0 hi B hb W f hk

def vector (W : WeightSpace R) (f : X R) : X R :=
  (readout_memLp μ R Q hQ α hα hα0 hi B hb W f).toLp _

theorem vector_ae (W : WeightSpace R) (f : X R) :
    vector μ R Q hQ α hα hα0 hi B hb W f=ᵐ[cubeVolume R] readout μ R Q α W f := MemLp.coeFn_toLp _

include hB in
theorem vector_norm_le (W : WeightSpace R) (f : X R) :
    ‖vector μ R Q hQ α hα hα0 hi B hb W f‖≤(B*‖W‖)*‖f‖ := by
  letI := cubeVolume_finite R
  have hAE : ∀ᵐk∂cubeVolume R,‖vector μ R Q hQ α hα hα0 hi B hb W f k‖≤(B*‖W‖)*‖f‖ := by
    filter_upwards [vector_ae μ R Q hQ α hα hα0 hi B hb W f,
      ae_restrict_mem (measurable_cube R)] with k he hk
    rw [he]
    exact readout_bound μ R Q hQ α hα0 hi B hb W f hk
  simpa using Lp.norm_le_of_ae_bound (by positivity : 0≤(B*‖W‖)*‖f‖) hAE

theorem vector_add_input (W : WeightSpace R) (f g : X R) :
    vector μ R Q hQ α hα hα0 hi B hb W (f+g)=
      vector μ R Q hQ α hα hα0 hi B hb W f+vector μ R Q hQ α hα hα0 hi B hb W g := by
  apply Lp.ext
  filter_upwards [vector_ae μ R Q hQ α hα hα0 hi B hb W (f+g),
    vector_ae μ R Q hQ α hα hα0 hi B hb W f,vector_ae μ R Q hQ α hα hα0 hi B hb W g,
    Lp.coeFn_add (vector μ R Q hQ α hα hα0 hi B hb W f)
      (vector μ R Q hQ α hα hα0 hi B hb W g),ae_restrict_mem (measurable_cube R)] with k hfg hf hg hs hk
  simp only [Pi.add_apply] at hs
  rw [hfg,hs,hf,hg]
  unfold readout
  rw [←integral_add (product_integrable μ R Q hQ α hα hα0 hi W f hk)
    (product_integrable μ R Q hQ α hα hα0 hi W g hk)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with p hp
  change (f+g) p=f p+g p at hp
  rw [hp,mul_add]

theorem vector_smul_input (W : WeightSpace R) (c : ℝ) (f : X R) :
    vector μ R Q hQ α hα hα0 hi B hb W (c • f)=
      c • vector μ R Q hQ α hα hα0 hi B hb W f := by
  apply Lp.ext
  filter_upwards [vector_ae μ R Q hQ α hα hα0 hi B hb W (c • f),
    vector_ae μ R Q hQ α hα hα0 hi B hb W f,
    Lp.coeFn_smul c (vector μ R Q hQ α hα hα0 hi B hb W f)] with k hcf hf hs
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  rw [hcf,hs,hf]
  unfold readout
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with p hp
  change (c • f) p=c*f p at hp
  rw [hp]
  ring

def inputLinear (W : WeightSpace R) : X R→ₗ[ℝ]X R where
  toFun := vector μ R Q hQ α hα hα0 hi B hb W
  map_add' := vector_add_input μ R Q hQ α hα hα0 hi B hb W
  map_smul' := vector_smul_input μ R Q hQ α hα hα0 hi B hb W

def inputOperator (W : WeightSpace R) : X R→L[ℝ]X R :=
  (inputLinear μ R Q hQ α hα hα0 hi B hb W).mkContinuous (B*‖W‖)
    (vector_norm_le μ R Q hQ α hα hα0 hi B hB hb W)

theorem inputOperator_ae (W : WeightSpace R) (f : X R) :
    inputOperator μ R Q hQ α hα hα0 hi B hB hb W f=ᵐ[cubeVolume R]
      readout μ R Q α W f := vector_ae μ R Q hQ α hα hα0 hi B hb W f

theorem inputOperator_norm_le (W : WeightSpace R) :
    ‖inputOperator μ R Q hQ α hα hα0 hi B hB hb W‖≤B*‖W‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg hB (norm_nonneg _)) _

theorem inputOperator_add_weight (V W : WeightSpace R) :
    inputOperator μ R Q hQ α hα hα0 hi B hB hb (V+W)=
      inputOperator μ R Q hQ α hα hα0 hi B hB hb V+
      inputOperator μ R Q hQ α hα hα0 hi B hB hb W := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [inputOperator_ae μ R Q hQ α hα hα0 hi B hB hb (V+W) f,
    inputOperator_ae μ R Q hQ α hα hα0 hi B hB hb V f,
    inputOperator_ae μ R Q hQ α hα hα0 hi B hB hb W f,
    Lp.coeFn_add (inputOperator μ R Q hQ α hα hα0 hi B hB hb V f)
      (inputOperator μ R Q hQ α hα hα0 hi B hB hb W f),
    ae_restrict_mem (measurable_cube R)] with k hvw hv hw hs hk
  change (inputOperator μ R Q hQ α hα hα0 hi B hB hb V f+
    inputOperator μ R Q hQ α hα hα0 hi B hB hb W f) k=_ at hs
  simp only [Pi.add_apply] at hs
  change inputOperator μ R Q hQ α hα hα0 hi B hB hb (V+W) f k=
    (inputOperator μ R Q hQ α hα hα0 hi B hB hb V f+
      inputOperator μ R Q hQ α hα hα0 hi B hB hb W f) k
  rw [hvw,hs,hv,hw]
  unfold readout
  rw [←integral_add (product_integrable μ R Q hQ α hα hα0 hi V f hk)
    (product_integrable μ R Q hQ α hα hα0 hi W f hk)]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  unfold kernel
  dsimp only
  rw [fiber_add μ R Q hQ]
  ring

theorem inputOperator_smul_weight (c : ℝ) (W : WeightSpace R) :
    inputOperator μ R Q hQ α hα hα0 hi B hB hb (c • W)=
      c • inputOperator μ R Q hQ α hα hα0 hi B hB hb W := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [inputOperator_ae μ R Q hQ α hα hα0 hi B hB hb (c • W) f,
    inputOperator_ae μ R Q hQ α hα hα0 hi B hB hb W f,
    Lp.coeFn_smul c (inputOperator μ R Q hQ α hα hα0 hi B hB hb W f)] with k hcw hw hs
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  change inputOperator μ R Q hQ α hα hα0 hi B hB hb (c • W) f k=
    (c • inputOperator μ R Q hQ α hα hα0 hi B hB hb W f) k
  rw [hcw,hs,hw]
  unfold readout
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  unfold kernel
  dsimp only
  rw [fiber_smul μ R Q]
  ring

def weightLinear : WeightSpace R→ₗ[ℝ](X R→L[ℝ]X R) where
  toFun := inputOperator μ R Q hQ α hα hα0 hi B hB hb
  map_add' := inputOperator_add_weight μ R Q hQ α hα hα0 hi B hB hb
  map_smul' := inputOperator_smul_weight μ R Q hQ α hα hα0 hi B hB hb

def weightOperator : WeightSpace R→L[ℝ](X R→L[ℝ]X R) :=
  (weightLinear μ R Q hQ α hα hα0 hi B hB hb).mkContinuous B
    (inputOperator_norm_le μ R Q hQ α hα hα0 hi B hB hb)

theorem weightOperator_norm_le : ‖weightOperator μ R Q hQ α hα hα0 hi B hB hb‖≤B :=
  LinearMap.mkContinuous_norm_le _ hB _

end
end Resonance.PairWeightLinear
