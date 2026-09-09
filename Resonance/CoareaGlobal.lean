import Resonance.CoareaNormalization
import Resonance.PolarCoordinates

open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace Resonance.CoareaGlobal
noncomputable section
set_option maxHeartbeats 800000

abbrev E := ResonantMeasure.E
abbrev Sphere := ResonantMeasure.Sphere
abbrev Radius := ResonantMeasure.Radius
abbrev Parameters := ResonantMeasure.Parameters
abbrev FourMomenta := ResonantMeasure.FourMomenta
open CoareaNormalization

/-- The unchanged first-radius polar volume, before energy elimination. -/
def polarBase : Measure Parameters :=
  (volume : Measure E).prod
    ((Measure.volumeIoiPow 2).prod (ResonantMeasure.surface.prod ResonantMeasure.surface))

instance : SigmaFinite polarBase := by unfold polarBase; infer_instance

def paramBox (R : ℝ) : Set Parameters :=
  {p | ‖p.1‖ ≤ 3 * R ∧ (p.2.1 : ℝ) ≤ 3 * R}

def truncatedBase (R : ℝ) : Measure Parameters := polarBase.restrict (paramBox R)

instance (R : ℝ) : SigmaFinite (truncatedBase R) := by
  unfold truncatedBase
  infer_instance

theorem paramBox_measurable (R : ℝ) : MeasurableSet (paramBox R) := by
  have h1 : MeasurableSet {p : Parameters | ‖p.1‖ ≤ 3 * R} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 : MeasurableSet {p : Parameters | (p.2.1 : ℝ) ≤ 3 * R} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter h2

theorem paramBox_finite {R : ℝ} (hR : 0 ≤ R) : polarBase (paramBox R) < ∞ := by
  let upper : Radius := ⟨3 * R + 1, by change 0 < 3 * R + 1; positivity⟩
  have hb : paramBox R ⊆ closedBall (0 : E) (3 * R) ×ˢ
      (Iio upper ×ˢ (univ : Set (Sphere × Sphere))) := by
    intro p hp
    exact ⟨by simpa [mem_closedBall, dist_zero_right] using hp.1,
      by change (p.2.1 : ℝ) < 3 * R + 1; linarith [hp.2], mem_univ _⟩
  apply lt_of_le_of_lt (measure_mono hb)
  rw [polarBase, Measure.prod_prod, Measure.prod_prod]
  have hV : (volume : Measure E) (closedBall 0 (3 * R)) < ∞ :=
    (isCompact_closedBall (0 : E) (3 * R)).measure_lt_top
  have hr : Measure.volumeIoiPow 2 (Iio upper) < ∞ := by
    rw [Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top
  exact ENNReal.mul_lt_top hV (ENNReal.mul_lt_top hr (measure_lt_top _ _))

theorem truncatedBase_finite {R : ℝ} (hR : 0 ≤ R) :
    IsFiniteMeasure (truncatedBase R) :=
  ⟨by simpa [truncatedBase] using paramBox_finite hR⟩

theorem pair_bounds {R : ℝ} (hR : 0 ≤ R) (V : E) {r : ℝ} (hr : 0 ≤ r)
    (σ : Sphere) (hplus : V + r • (σ : E) ∈ ResonantMeasure.cube R)
    (hminus : V - r • (σ : E) ∈ ResonantMeasure.cube R) :
    ‖V‖ ≤ 3 * R ∧ r ≤ 3 * R := by
  have h0 := ResonantMeasure.norm_le_three_R hR hplus
  have h1 := ResonantMeasure.norm_le_three_R hR hminus
  have ha := norm_add_le (V + r • (σ : E)) (V - r • (σ : E))
  have hs := norm_sub_le (V + r • (σ : E)) (V - r • (σ : E))
  have ea : (V + r • (σ : E)) + (V - r • (σ : E)) = (2 : ℝ) • V := by
    simp [two_smul]
  have es : (V + r • (σ : E)) - (V - r • (σ : E)) = (2 * r) • (σ : E) := by
    simp [sub_eq_add_neg, add_smul, two_mul, add_left_comm, add_assoc]
  rw [ea, norm_smul] at ha
  rw [es, norm_smul] at hs
  simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2*r),
    norm_eq_of_mem_sphere, mul_one] at hs
  constructor <;> nlinarith

/-- Both radii and all four original flags remain in this off-shell map. -/
def energyShell (p : Parameters) (e : ℝ) : FourMomenta :=
  radialFour p.1 p.2.1 p.2.2.1 (energyRadius p.2.1 e) p.2.2.2

def density (R : ℝ) (Φ : FourMomenta → ℝ) (e : ℝ) (p : Parameters) : ℝ :=
  energyRadius p.2.1 e / 4 * sharpReadout R Φ (energyShell p e)

theorem energyShell_continuous :
    Continuous (fun x : ℝ × Parameters => energyShell x.2 x.1) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [energyShell, radialFour, energyRadius] <;> fun_prop

theorem density_measurable (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun x : ℝ × Parameters => density R Φ x.1 x.2) := by
  unfold density
  exact (by unfold energyRadius; fun_prop : Measurable (fun x : ℝ × Parameters => energyRadius x.2.2.1 x.1 / 4)).mul
    ((sharpReadout_measurable R hΦ).comp energyShell_continuous.measurable)

theorem density_nonzero_flags {R : ℝ} {Φ : FourMomenta → ℝ} {e : ℝ} {p : Parameters}
    (h : density R Φ e p ≠ 0) :
    energyShell p e ∈ allFourFlags R ∧ 0 < energyRadius p.2.1 e := by
  constructor
  · by_contra hn
    simp [density, sharpReadout, Set.indicator_of_notMem hn] at h
  · by_contra hn
    have hz : energyRadius p.2.1 e = 0 :=
      le_antisymm (le_of_not_gt hn) (Real.sqrt_nonneg _)
    simp [density, hz] at h

theorem density_nonzero_bounds {R : ℝ} (hR : 0 ≤ R) {Φ : FourMomenta → ℝ}
    {e : ℝ} {p : Parameters} (h : density R Φ e p ≠ 0) :
    p ∈ paramBox R ∧ energyRadius p.2.1 e ≤ 3 * R ∧
      e ∈ Icc (-18 * R ^ 2) (18 * R ^ 2) := by
  obtain ⟨hf, hspos⟩ := density_nonzero_flags h
  have hin := pair_bounds hR p.1 p.2.1.property.le p.2.2.1 (hf 0) (hf 1)
  have hout := pair_bounds hR p.1 hspos.le p.2.2.2 (hf 2) (hf 3)
  have hsrad : 0 < (p.2.1 : ℝ)^2 - e/2 := Real.sqrt_pos.mp hspos
  have hs2 := Real.sq_sqrt hsrad.le
  change (Real.sqrt ((p.2.1 : ℝ)^2 - e/2))^2 = _ at hs2
  have hrpos : 0 < (p.2.1 : ℝ) := p.2.1.property
  have hsbound : Real.sqrt ((p.2.1 : ℝ)^2 - e/2) ≤ 3 * R := hout.2
  have hr2 := pow_le_pow_left₀ hrpos.le hin.2 2
  have hs2b := pow_le_pow_left₀ (Real.sqrt_nonneg ((p.2.1 : ℝ)^2 - e/2)) hsbound 2
  refine ⟨hin, hout.2, ?_, ?_⟩ <;> nlinarith [sq_nonneg (p.2.1 : ℝ)]

theorem density_norm_bound {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) (e : ℝ) (p : Parameters) :
    ‖density R Φ e p‖ ≤ (3 * R / 4) * B := by
  by_cases hz : density R Φ e p = 0
  · rw [hz, norm_zero]
    positivity
  · have hb := density_nonzero_bounds hR hz
    have hf := (density_nonzero_flags hz).1
    have hnonneg : 0 ≤ energyRadius p.2.1 e / 4 :=
      div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    rw [density, sharpReadout, Set.indicator_of_mem hf, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact mul_le_mul (by linarith [hb.2.1]) (hΦ _ hf) (norm_nonneg _) (by positivity)

theorem density_zero_outside_paramBox {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (e : ℝ) {p : Parameters} (hp : p ∉ paramBox R) :
    density R Φ e p = 0 := by
  by_contra hz
  exact hp (density_nonzero_bounds hR hz).1

theorem density_zero_outside_energyBand {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) {e : ℝ} (he : e ∉ Icc (-18*R^2) (18*R^2))
    (p : Parameters) : density R Φ e p = 0 := by
  by_contra hz
  exact he (density_nonzero_bounds hR hz).2.2

/-- Full energy density after the genuine radial change, integrated over all remaining parameters. -/
def globalEnergy (R : ℝ) (Φ : FourMomenta → ℝ) (e : ℝ) : ℝ :=
  ∫ p, density R Φ e p ∂truncatedBase R

theorem density_integrable {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ) (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) (e : ℝ) :
    Integrable (density R Φ e) (truncatedBase R) := by
  letI := truncatedBase_finite hR
  have hm : Measurable (density R Φ e) :=
    (density_measurable R hΦm).comp (measurable_const.prodMk measurable_id)
  have hc : Integrable (fun _ : Parameters => (3*R/4)*B) (truncatedBase R) :=
    integrable_const _
  exact hc.mono' hm.aestronglyMeasurable
    (ae_of_all _ (density_norm_bound hR hB Φ hΦ e))

theorem globalEnergy_measurable (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Measurable Φ) :
    Measurable (globalEnergy R Φ) := by
  have h := (density_measurable R hΦ).stronglyMeasurable.integral_prod_right'
    (ν := truncatedBase R)
  exact h.measurable

theorem globalEnergy_norm_bound {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) (e : ℝ) :
    ‖globalEnergy R Φ e‖ ≤ ((3*R/4)*B) * (truncatedBase R).real univ := by
  letI := truncatedBase_finite hR
  exact norm_integral_le_of_norm_le_const (ae_of_all _
    (density_norm_bound hR hB Φ hΦ e))

theorem globalEnergy_zero_outside_band {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) {e : ℝ} (he : e ∉ Icc (-18*R^2) (18*R^2)) :
    globalEnergy R Φ e = 0 := by
  have hz : density R Φ e = 0 := funext (density_zero_outside_energyBand hR Φ he)
  simp only [globalEnergy, hz, Pi.zero_apply, integral_zero]

theorem globalEnergy_integrable {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ) (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) :
    Integrable (globalEnergy R Φ) := by
  let C : ℝ := ((3*R/4)*B) * (truncatedBase R).real univ
  have hc : Integrable ((Icc (-18*R^2) (18*R^2)).indicator (fun _ : ℝ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (isCompact_Icc.measure_ne_top))
  apply hc.mono' (globalEnergy_measurable R hΦm).aestronglyMeasurable
  apply ae_of_all
  intro e
  by_cases he : e ∈ Icc (-18*R^2) (18*R^2)
  · simpa only [Set.indicator_of_mem he] using globalEnergy_norm_bound hR hB Φ hΦ e
  · rw [Set.indicator_of_notMem he, globalEnergy_zero_outside_band hR Φ he, norm_zero]

/-- A Euclidean coordinate hyperplane has zero original volume. -/
theorem euclidean_coordinate_face_null (j : Fin 3) (a : ℝ) :
    (volume : Measure E) {k | k j = a} = 0 := by
  have hm : MeasurableSet {k : E | k j = a} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hpre := toMomentumE_volume_preserving.measure_preimage hm.nullMeasurableSet
  have hz : (volume : Measure Thermodynamics.Momentum)
      (toMomentumE ⁻¹' {k : E | k j = a}) = 0 := by
    change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) {p | p j = a} = 0
    exact Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) j a
  exact hpre.symm.trans hz

theorem euclidean_absolute_face_null (j : Fin 3) (R : ℝ) :
    (volume : Measure E) {k | |k j| = R} = 0 := by
  have hs : {k : E | |k j| = R} ⊆ {k | k j = R} ∪ {k | k j = -R} := by
    intro k hk
    exact eq_or_eq_neg_of_abs_eq hk
  apply measure_mono_null hs
  exact measure_union_null (euclidean_coordinate_face_null j R)
    (euclidean_coordinate_face_null j (-R))

/-- Boundary exceptional sets are paid on the common center V, not on individual sphere charts. -/
theorem polarBase_single_leg_null (i : Fin 4) {s : Set E} (hs : MeasurableSet s)
    (hzero : (volume : Measure E) s = 0) :
    polarBase ((fun p => ResonantMeasure.paired p i) ⁻¹' s) = 0 := by
  have hset : MeasurableSet ((fun p : Parameters => ResonantMeasure.paired p i) ⁻¹' s) :=
    hs.preimage ((measurable_pi_apply i).comp ResonantMeasure.continuous_paired.measurable)
  rw [polarBase, Measure.prod_apply_symm hset]
  have hsection (b : Radius × (Sphere × Sphere)) :
      (volume : Measure E) ((fun V : E => (V, b)) ⁻¹'
        ((fun p => ResonantMeasure.paired p i) ⁻¹' s)) = 0 := by
    have he : ((fun V : E => (V, b)) ⁻¹' ((fun p => ResonantMeasure.paired p i) ⁻¹' s)) =
        (fun V : E => V + ResonantMeasure.legShift i b) ⁻¹' s := by
      ext V
      simp only [mem_preimage, ResonantMeasure.paired_leg_translate]
    rw [he]
    simpa only [id_eq] using (((MeasurePreserving.id (volume : Measure E)).add_right
      (volume : Measure E) (ResonantMeasure.legShift i b)).measure_preimage
        hs.nullMeasurableSet).trans hzero
  simp_rw [hsection]
  simp

theorem ae_all_faces_avoided (R : ℝ) :
    ∀ᵐ p ∂polarBase, ∀ i : Fin 4, ∀ j : Fin 3, |ResonantMeasure.paired p i j| ≠ R := by
  apply Filter.eventually_all.2
  intro i
  apply Filter.eventually_all.2
  intro j
  have hm : MeasurableSet {k : E | |k j| = R} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hz := polarBase_single_leg_null i hm (euclidean_absolute_face_null j R)
  apply ae_iff.mpr
  simpa only [not_not] using hz

theorem energyShell_at_zero (p : Parameters) :
    energyShell p 0 = ResonantMeasure.paired p := by
  have hr : energyRadius p.2.1 0 = (p.2.1 : ℝ) := by
    simp [energyRadius, Real.sqrt_sq p.2.1.property.le]
  rw [energyShell, hr]
  exact radialFour_on_level p

theorem eventually_le_iff_of_continuousAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousAt f a) (hne : f a ≠ b) :
    ∀ᶠ e in nhds a, (f e ≤ b ↔ f a ≤ b) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he := hf.tendsto.eventually (isOpen_Iio.mem_nhds hlt)
    filter_upwards [he] with e he
    exact iff_of_true (le_of_lt he) hlt.le
  · have he := hf.tendsto.eventually (isOpen_Ioi.mem_nhds hgt)
    filter_upwards [he] with e he
    exact iff_of_false (not_le_of_gt he) (not_le_of_gt hgt)

theorem sharp_shell_continuousAt_zero (R : ℝ) {Φ : FourMomenta → ℝ}
    (hΦ : Continuous Φ) (p : Parameters)
    (hp : ∀ i : Fin 4, ∀ j : Fin 3, |ResonantMeasure.paired p i j| ≠ R) :
    ContinuousAt (fun e => sharpReadout R Φ (energyShell p e)) 0 := by
  have hc : Continuous (fun e => energyShell p e) :=
    energyShell_continuous.comp (continuous_id.prodMk continuous_const)
  have hcoords : ∀ᶠ e in nhds (0 : ℝ), ∀ i : Fin 4, ∀ j : Fin 3,
      (|energyShell p e i j| ≤ R ↔ |ResonantMeasure.paired p i j| ≤ R) := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro j
    have hcc : Continuous (fun e => |energyShell p e i j|) := by
      have hout : Continuous (fun k : FourMomenta => |k i j|) := by fun_prop
      exact hout.comp hc
    have hne : |energyShell p 0 i j| ≠ R := by
      rw [energyShell_at_zero]
      exact hp i j
    have hh := eventually_le_iff_of_continuousAt (a := 0) (b := R)
      hcc.continuousAt hne
    simpa only [energyShell_at_zero] using hh
  have hflags : ∀ᶠ e in nhds (0 : ℝ),
      (energyShell p e ∈ allFourFlags R ↔ ResonantMeasure.paired p ∈ allFourFlags R) := by
    filter_upwards [hcoords] with e he
    change (∀ i, ∀ j, |energyShell p e i j| ≤ R) ↔
      (∀ i, ∀ j, |ResonantMeasure.paired p i j| ≤ R)
    exact forall_congr' fun i => forall_congr' fun j => he i j
  by_cases h0 : ResonantMeasure.paired p ∈ allFourFlags R
  · have heq : (fun e => sharpReadout R Φ (energyShell p e)) =ᶠ[nhds 0]
        (fun e => Φ (energyShell p e)) := by
      filter_upwards [hflags] with e he
      exact Set.indicator_of_mem (he.mpr h0) Φ
    change Filter.Tendsto (fun e => sharpReadout R Φ (energyShell p e))
      (nhds 0) (nhds (sharpReadout R Φ (energyShell p 0)))
    rw [energyShell_at_zero, sharpReadout, Set.indicator_of_mem h0]
    simpa only [Function.comp_apply, energyShell_at_zero] using (hΦ.comp hc).continuousAt.tendsto.congr' heq.symm
  · have heq : (fun e => sharpReadout R Φ (energyShell p e)) =ᶠ[nhds 0] (fun _ => (0:ℝ)) := by
      filter_upwards [hflags] with e he
      exact Set.indicator_of_notMem (fun hh => h0 (he.mp hh)) Φ
    change Filter.Tendsto (fun e => sharpReadout R Φ (energyShell p e))
      (nhds 0) (nhds (sharpReadout R Φ (energyShell p 0)))
    rw [energyShell_at_zero, sharpReadout, Set.indicator_of_notMem h0]
    exact tendsto_const_nhds.congr' heq.symm

theorem density_continuousAt_zero_ae (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Continuous Φ) :
    ∀ᵐ p ∂polarBase, ContinuousAt (fun e => density R Φ e p) 0 := by
  filter_upwards [ae_all_faces_avoided R] with p hp
  have hf : ContinuousAt (fun e => energyRadius p.2.1 e / 4) 0 := by
    unfold energyRadius
    fun_prop
  exact hf.mul (sharp_shell_continuousAt_zero R hΦ p hp)

theorem globalEnergy_continuousAt_zero {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦc : Continuous Φ) (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) :
    ContinuousAt (globalEnergy R Φ) 0 := by
  letI := truncatedBase_finite hR
  have hi : Integrable (fun _ : Parameters => (3*R/4)*B) (truncatedBase R) :=
    integrable_const _
  have ha : ∀ᵐ p ∂truncatedBase R, ContinuousAt (fun e => density R Φ e p) 0 :=
    ae_restrict_of_ae (density_continuousAt_zero_ae R hΦc)
  change Filter.Tendsto (fun e => ∫ p, density R Φ e p ∂truncatedBase R)
    (nhds 0) (nhds (∫ p, density R Φ 0 p ∂truncatedBase R))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (3*R/4)*B)
  · exact Filter.Eventually.of_forall fun e =>
      (density_integrable hR hB Φ hΦc.measurable hΦ e).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun e =>
      ae_of_all _ (density_norm_bound hR hB Φ hΦ e)
  · exact hi
  · exact ha.mono fun _ hp => hp.tendsto

/-- A genuine all-parameter weak energy limit with the four sharp flags still inside H. -/
theorem global_energy_peak_limit {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦc : Continuous Φ) (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) :
    Filter.Tendsto
      (fun c : ℝ => ∫ e, (c * boxKernel (c * e)) * globalEnergy R Φ e)
      Filter.atTop (nhds (globalEnergy R Φ 0)) := by
  have hi := globalEnergy_integrable hR hB Φ hΦc.measurable hΦ
  have hc := globalEnergy_continuousAt_zero hR hB Φ hΦc hΦ
  have ht := tendsto_integral_comp_smul_smul_of_integrable
    boxKernel_nonneg boxKernel_integral (by simpa using boxKernel_tail) hi hc
  simpa [smul_eq_mul] using ht

def layerKernel (c e : ℝ) : ℝ := c * boxKernel (c * e)

theorem layerKernel_measurable (c : ℝ) : Measurable (layerKernel c) := by
  have hb : Measurable boxKernel := measurable_const.indicator measurableSet_Icc
  exact measurable_const.mul (hb.comp (measurable_const.mul measurable_id))

theorem boxKernel_norm_bound (e : ℝ) : ‖boxKernel e‖ ≤ (1/2 : ℝ) := by
  by_cases he : e ∈ Icc (-1 : ℝ) 1 <;> simp [boxKernel, he]

theorem layerKernel_norm_bound (c e : ℝ) : ‖layerKernel c e‖ ≤ |c|/2 := by
  rw [layerKernel, norm_mul, Real.norm_eq_abs]
  nlinarith [boxKernel_norm_bound (c*e), abs_nonneg c]

theorem weighted_density_joint_integrable {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) (c : ℝ) :
    Integrable (fun x : ℝ × Parameters => layerKernel c x.1 * density R Φ x.1 x.2)
      ((volume : Measure ℝ).prod (truncatedBase R)) := by
  letI := truncatedBase_finite hR
  let C : ℝ := (|c|/2)*((3*R/4)*B)
  have hc : Integrable ((Icc (-18*R^2) (18*R^2)).indicator (fun _ : ℝ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (isCompact_Icc.measure_ne_top))
  have hp : Integrable (fun _ : Parameters => (1:ℝ)) (truncatedBase R) := integrable_const _
  have hmajor := hc.mul_prod hp
  have hm : Measurable (fun x : ℝ × Parameters =>
      layerKernel c x.1 * density R Φ x.1 x.2) :=
    ((layerKernel_measurable c).comp measurable_fst).mul (density_measurable R hΦm)
  apply hmajor.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [mul_one]
  by_cases he : x.1 ∈ Icc (-18*R^2) (18*R^2)
  · rw [Set.indicator_of_mem he, norm_mul]
    exact mul_le_mul (layerKernel_norm_bound c x.1)
      (density_norm_bound hR hB Φ hΦ x.1 x.2) (norm_nonneg _) (by positivity)
  · rw [Set.indicator_of_notMem he, density_zero_outside_energyBand hR Φ he,
      mul_zero, norm_zero]

def rawSlice (R : ℝ) (Φ : FourMomenta → ℝ) (c : ℝ) (p : Parameters) : ℝ :=
  ∫ s in Ioi 0, s^2 * sharpReadout R Φ
    (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2) *
      layerKernel c (energy (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2))

theorem rawSlice_energy_identity (R : ℝ) (Φ : FourMomenta → ℝ) (c : ℝ) (p : Parameters) :
    rawSlice R Φ c p = ∫ e, layerKernel c e * density R Φ e p := by
  unfold rawSlice
  simp_rw [radialFour_energy]
  rw [radial_energy_change_global]
  apply integral_congr_ae
  apply ae_of_all
  intro e
  dsimp [radialDensity, density, energyShell]
  ring

theorem truncated_rawSlice_integral {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) (c : ℝ) :
    (∫ p, rawSlice R Φ c p ∂truncatedBase R) =
      ∫ e, layerKernel c e * globalEnergy R Φ e := by
  have hj := weighted_density_joint_integrable hR hB Φ hΦm hΦ c
  simp_rw [rawSlice_energy_identity]
  rw [← integral_integral_swap hj]
  apply integral_congr_ae
  apply ae_of_all
  intro e
  exact integral_const_mul _ _

theorem rawSlice_zero_outside_box {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (c : ℝ) {p : Parameters} (hp : p ∉ paramBox R) :
    rawSlice R Φ c p = 0 := by
  have hz (e : ℝ) : density R Φ e p = 0 := density_zero_outside_paramBox hR Φ e hp
  rw [rawSlice_energy_identity]
  simp_rw [hz, mul_zero]
  exact integral_zero ℝ ℝ

theorem rawSlice_integral_full {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) (c : ℝ) :
    (∫ p, rawSlice R Φ c p ∂polarBase) =
      ∫ e, layerKernel c e * globalEnergy R Φ e := by
  have he : (∫ p, rawSlice R Φ c p ∂truncatedBase R) =
      ∫ p, rawSlice R Φ c p ∂polarBase :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => rawSlice_zero_outside_box hR Φ c hp)
  rw [← he]
  exact truncated_rawSlice_integral hR hB Φ hΦm hΦ c

theorem globalEnergy_full_integral {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (e : ℝ) :
    globalEnergy R Φ e = ∫ p, density R Φ e p ∂polarBase :=
  setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun _ hp => density_zero_outside_paramBox hR Φ e hp)

theorem density_at_zero (R : ℝ) (Φ : FourMomenta → ℝ) (p : Parameters) :
    density R Φ 0 p = (p.2.1 : ℝ)/4 *
      (ResonantMeasure.allowed R).indicator (fun p => Φ (ResonantMeasure.paired p)) p := by
  have hr : energyRadius p.2.1 0 = (p.2.1 : ℝ) := by
    simp [energyRadius, Real.sqrt_sq p.2.1.property.le]
  rw [density, hr, energyShell_at_zero]
  rfl

theorem pairing_eq_eight_globalEnergy {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ) :
    (∫ k, Φ k ∂(ResonantMeasure.pairingMeasure R)) = 8 * globalEnergy R Φ 0 := by
  rw [globalEnergy_full_integral hR Φ 0, PolarCoordinates.pairing_integral R Φ hΦm]
  change 2 * (∫ p, (p.2.1 : ℝ) *
      (ResonantMeasure.allowed R).indicator (fun p => Φ (ResonantMeasure.paired p)) p ∂polarBase) =
    8 * ∫ p, density R Φ 0 p ∂polarBase
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [density_at_zero]
  ring

/-- The full sharp readout has a genuine all-parameter limit equal to the frozen pairing measure.
The original Cartesian root below supplies the proved double-polar transport. -/
theorem full_radial_sharp_limit {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦc : Continuous Φ)
    (hΦ : ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B) :
    Filter.Tendsto (fun c : ℝ => 8 * ∫ p, rawSlice R Φ c p ∂polarBase)
      Filter.atTop (nhds (∫ k, Φ k ∂(ResonantMeasure.pairingMeasure R))) := by
  simp_rw [rawSlice_integral_full hR hB Φ hΦc.measurable hΦ]
  rw [pairing_eq_eight_globalEnergy hR Φ hΦc.measurable]
  exact Filter.Tendsto.const_mul 8 (global_energy_peak_limit hR hB Φ hΦc hΦ)

/-- The original nine-dimensional sharp energy layers converge to the same frozen
pairing measure for every continuous whole-four-leg test. No global boundedness,
Fubini, domination, boundary, or measure-identification premise is assumed. -/
theorem original_sharp_coarea_limit {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Filter.Tendsto
      (fun c : ℝ => ∫ z : Nine,
        PolarCoordinates.sharpLayer R c Φ (physicalFour z))
      Filter.atTop (nhds (∫ k, Φ k ∂(ResonantMeasure.pairingMeasure R))) := by
  obtain ⟨B, hB, hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  have ht := full_radial_sharp_limit hR hB Φ hΦ hbound
  have he (c : ℝ) :
      (∫ z : Nine, PolarCoordinates.sharpLayer R c Φ (physicalFour z)) =
        8 * ∫ p, rawSlice R Φ c p ∂polarBase := by
    simpa only [rawSlice, layerKernel, radialFour_energy] using
      PolarCoordinates.original_sharp_layer_doublePolar hR c Φ hΦ
  exact ht.congr' (Filter.Eventually.of_forall fun c => (he c).symm)

/-- Expanded original-root statement: all four indicators and the complete
energy difference are visible, with the physical Cartesian volume. -/
theorem full_sharp_energy_layer_limit {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Filter.Tendsto
      (fun c : ℝ => ∫ z : Nine,
        sharpReadout R Φ (physicalFour z) *
          (c * boxKernel (c * energy (physicalFour z))))
      Filter.atTop (nhds (∫ k, Φ k ∂(ResonantMeasure.pairingMeasure R))) := by
  simpa only [PolarCoordinates.sharpLayer] using original_sharp_coarea_limit hR Φ hΦ


/-! Exact theorem types and logical dependency audit. -/
#check paramBox_measurable
#print axioms paramBox_measurable
#check paramBox_finite
#print axioms paramBox_finite
#check truncatedBase_finite
#print axioms truncatedBase_finite
#check pair_bounds
#print axioms pair_bounds
#check energyShell_continuous
#print axioms energyShell_continuous
#check density_measurable
#print axioms density_measurable
#check density_nonzero_flags
#print axioms density_nonzero_flags
#check density_nonzero_bounds
#print axioms density_nonzero_bounds
#check density_norm_bound
#print axioms density_norm_bound
#check density_zero_outside_paramBox
#print axioms density_zero_outside_paramBox
#check density_zero_outside_energyBand
#print axioms density_zero_outside_energyBand
#check density_integrable
#print axioms density_integrable
#check globalEnergy_measurable
#print axioms globalEnergy_measurable
#check globalEnergy_norm_bound
#print axioms globalEnergy_norm_bound
#check globalEnergy_zero_outside_band
#print axioms globalEnergy_zero_outside_band
#check globalEnergy_integrable
#print axioms globalEnergy_integrable
#check euclidean_coordinate_face_null
#print axioms euclidean_coordinate_face_null
#check euclidean_absolute_face_null
#print axioms euclidean_absolute_face_null
#check polarBase_single_leg_null
#print axioms polarBase_single_leg_null
#check ae_all_faces_avoided
#print axioms ae_all_faces_avoided
#check energyShell_at_zero
#print axioms energyShell_at_zero
#check eventually_le_iff_of_continuousAt
#print axioms eventually_le_iff_of_continuousAt
#check sharp_shell_continuousAt_zero
#print axioms sharp_shell_continuousAt_zero
#check density_continuousAt_zero_ae
#print axioms density_continuousAt_zero_ae
#check globalEnergy_continuousAt_zero
#print axioms globalEnergy_continuousAt_zero
#check global_energy_peak_limit
#print axioms global_energy_peak_limit
#check layerKernel_measurable
#print axioms layerKernel_measurable
#check boxKernel_norm_bound
#print axioms boxKernel_norm_bound
#check layerKernel_norm_bound
#print axioms layerKernel_norm_bound
#check weighted_density_joint_integrable
#print axioms weighted_density_joint_integrable
#check rawSlice_energy_identity
#print axioms rawSlice_energy_identity
#check truncated_rawSlice_integral
#print axioms truncated_rawSlice_integral
#check rawSlice_zero_outside_box
#print axioms rawSlice_zero_outside_box
#check rawSlice_integral_full
#print axioms rawSlice_integral_full
#check globalEnergy_full_integral
#print axioms globalEnergy_full_integral
#check density_at_zero
#print axioms density_at_zero
#check pairing_eq_eight_globalEnergy
#print axioms pairing_eq_eight_globalEnergy
#check full_radial_sharp_limit
#print axioms full_radial_sharp_limit
#check original_sharp_coarea_limit
#print axioms original_sharp_coarea_limit
#check full_sharp_energy_layer_limit
#print axioms full_sharp_energy_layer_limit

end
end Resonance.CoareaGlobal
