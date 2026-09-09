import Resonance.PlaneCoarea

open MeasureTheory Set Metric
open scoped ENNReal NNReal EuclideanGeometry
namespace Resonance.PlaneGlobal
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea

abbrev PlaneParameters := E × (Ray × E2)

def radialOne : Measure Radius := Measure.volumeIoiPow 1
instance : SigmaFinite radialOne :=
  inferInstanceAs (SigmaFinite (Measure.volumeIoiPow 1))
def rayOne : Measure Ray := ResonantMeasure.surface.prod radialOne
instance : SigmaFinite rayOne := by unfold rayOne; infer_instance

def planeBase : Measure PlaneParameters :=
  (volume : Measure E).prod
    (rayOne.prod (volume : Measure E2))
instance : SigmaFinite planeBase := by unfold planeBase; infer_instance

def planeBox (R : ℝ) : Set PlaneParameters :=
  {p | ‖p.1‖ ≤ 3*R ∧ (p.2.1.2 : ℝ) ≤ 6*R ∧ ‖p.2.2‖ ≤ 6*R}
def planeTruncated (R : ℝ) : Measure PlaneParameters := planeBase.restrict (planeBox R)
instance (R : ℝ) : SigmaFinite (planeTruncated R) := by unfold planeTruncated; infer_instance

theorem planeBox_measurable (R : ℝ) : MeasurableSet (planeBox R) := by
  have h1 : MeasurableSet {p : PlaneParameters | ‖p.1‖ ≤ 3*R} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 : MeasurableSet {p : PlaneParameters | (p.2.1.2:ℝ) ≤ 6*R} :=
    measurableSet_le (by fun_prop) measurable_const
  have h3 : MeasurableSet {p : PlaneParameters | ‖p.2.2‖ ≤ 6*R} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter (h2.inter h3)

theorem planeBox_finite {R : ℝ} (hR : 0 ≤ R) :
    planeBase (planeBox R) < ∞ := by
  let upper : Radius := ⟨6*R+1, by change 0<6*R+1; positivity⟩
  have hb : planeBox R ⊆ closedBall (0:E) (3*R) ×ˢ
      (((univ : Set Sphere) ×ˢ Iio upper) ×ˢ closedBall (0:E2) (6*R)) := by
    intro p hp
    exact ⟨by simpa [mem_closedBall,dist_zero_right] using hp.1,
      ⟨mem_univ _,by change (p.2.1.2:ℝ)<6*R+1; linarith [hp.2.1]⟩,
      by simpa [mem_closedBall,dist_zero_right] using hp.2.2⟩
  apply lt_of_le_of_lt (measure_mono hb)
  rw [planeBase, Measure.prod_prod, Measure.prod_prod, rayOne, Measure.prod_prod]
  apply ENNReal.mul_lt_top (isCompact_closedBall (0:E) (3*R)).measure_lt_top
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top (measure_lt_top _ _)
    rw [radialOne, Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top
  · exact (isCompact_closedBall (0:E2) (6*R)).measure_lt_top

theorem planeTruncated_finite {R : ℝ} (hR : 0 ≤ R) :
    IsFiniteMeasure (planeTruncated R) :=
  ⟨by simpa [planeTruncated] using planeBox_finite hR⟩

def planeShell (p : PlaneParameters) (e : ℝ) : FourMomenta :=
  rectangleFour p.1 ((p.2.1.2:ℝ) • (p.2.1.1:E))
    (normalCoords p.2.1.1 (e/(2*(p.2.1.2:ℝ)),p.2.2))

theorem planeShell_energy (p : PlaneParameters) (e : ℝ) :
    CoareaNormalization.energy (planeShell p e) = e := by
  rw [planeShell, normal_energy]
  have hr : (p.2.1.2:ℝ) ≠ 0 := ne_of_gt p.2.1.2.property
  field_simp

theorem planeShell_joint_measurable :
    Measurable (fun x : ℝ × PlaneParameters => planeShell x.2 x.1) := by
  have hm : Measurable (fun x : ℝ × PlaneParameters =>
      (x.2.2.1.1,(x.1/(2*(x.2.2.1.2:ℝ)),x.2.2.2))) := by fun_prop
  have hn := normalCoords_joint_measurable.comp hm
  have hr : Measurable (fun x : ℝ × PlaneParameters =>
      (x.2.1,((x.2.2.1.2:ℝ) • (x.2.2.1.1:E),
        normalCoords x.2.2.1.1 (x.1/(2*(x.2.2.1.2:ℝ)),x.2.2.2)))) := by
    exact (by fun_prop : Measurable (fun x : ℝ × PlaneParameters => x.2.1)).prodMk
      ((by fun_prop : Measurable (fun x : ℝ × PlaneParameters =>
        (x.2.2.1.2:ℝ) • (x.2.2.1.1:E))).prodMk
          (by simpa only [Function.comp_def] using hn))
  have hh := rectangleFour_continuous.measurable.comp hr
  simpa only [Function.comp_def, planeShell] using hh

theorem planeShell_continuous (p : PlaneParameters) :
    Continuous (planeShell p) := by
  have hm : Continuous (fun e : ℝ => (e/(2*(p.2.1.2:ℝ)),p.2.2)) := by fun_prop
  have hn := (normalCoords_continuous p.2.1.1).comp hm
  have ht : Continuous (fun e : ℝ =>
      (p.1,((p.2.1.2:ℝ) • (p.2.1.1:E), normalCoords p.2.1.1 (e/(2*(p.2.1.2:ℝ)),p.2.2)))) := by
    exact continuous_const.prodMk (continuous_const.prodMk hn)
  have hh := rectangleFour_continuous.comp ht
  simpa only [Function.comp_def, planeShell] using hh

theorem rectangle_flags_bounds {R : ℝ} (hR : 0 ≤ R) (k x y : E)
    (hf : rectangleFour k x y ∈ CoareaNormalization.allFourFlags R) :
    ‖k‖ ≤ 3*R ∧ ‖x‖ ≤ 6*R ∧ ‖y‖ ≤ 6*R := by
  have hk := ResonantMeasure.norm_le_three_R hR (hf 0)
  have hx := ResonantMeasure.norm_le_three_R hR (hf 2)
  have hy := ResonantMeasure.norm_le_three_R hR (hf 3)
  change ‖k‖ ≤ 3*R at hk
  change ‖k+x‖ ≤ 3*R at hx
  change ‖k+y‖ ≤ 3*R at hy
  have hx' := norm_sub_le (k+x) k
  have hy' := norm_sub_le (k+y) k
  simp only [add_sub_cancel_left] at hx' hy'
  exact ⟨hk,by linarith,by linarith⟩

theorem planeShell_flags_bounds {R : ℝ} (hR : 0 ≤ R) (p : PlaneParameters) (e : ℝ)
    (hf : planeShell p e ∈ CoareaNormalization.allFourFlags R) :
    p ∈ planeBox R ∧ e ∈ Icc (-72*R^2) (72*R^2) := by
  have hb := rectangle_flags_bounds hR p.1 ((p.2.1.2:ℝ) • (p.2.1.1:E))
    (normalCoords p.2.1.1 (e/(2*(p.2.1.2:ℝ)),p.2.2)) hf
  have hr : (p.2.1.2:ℝ) ≤ 6*R := by
    have hrpos : 0 < (p.2.1.2:ℝ) := p.2.1.2.property
    simpa [norm_smul,abs_of_pos hrpos] using hb.2.1
  have hz := (normalCoords_transverse_bound p.2.1.1
    (e/(2*(p.2.1.2:ℝ))) p.2.2).trans hb.2.2
  have he : |e| ≤ 72*R^2 := by
    rw [← planeShell_energy p e, planeShell, rectangleFour_energy, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hi := abs_real_inner_le_norm ((p.2.1.2:ℝ) • (p.2.1.1:E))
      (normalCoords p.2.1.1 (e/(2*(p.2.1.2:ℝ)),p.2.2))
    have hh := mul_le_mul hb.2.1 hb.2.2 (norm_nonneg _) (by positivity : 0 ≤ 6*R)
    nlinarith
  exact ⟨⟨hb.1,hr,hz⟩,by simpa only [neg_mul] using neg_le_of_abs_le he,le_of_abs_le he⟩

def planeDensity (R : ℝ) (Φ : FourMomenta → ℝ) (e : ℝ) (p : PlaneParameters) : ℝ :=
  (1/2:ℝ) * CoareaNormalization.sharpReadout R Φ (planeShell p e)

theorem planeDensity_measurable (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun x : ℝ × PlaneParameters => planeDensity R Φ x.1 x.2) :=
  measurable_const.mul ((CoareaNormalization.sharpReadout_measurable R hΦ).comp
    planeShell_joint_measurable)

theorem planeDensity_zero_outside_box {R : ℝ} (hR : 0 ≤ R) (Φ : FourMomenta → ℝ)
    (e : ℝ) {p : PlaneParameters} (hp : p ∉ planeBox R) :
    planeDensity R Φ e p = 0 := by
  have hn : planeShell p e ∉ CoareaNormalization.allFourFlags R :=
    fun hf => hp (planeShell_flags_bounds hR p e hf).1
  simp [planeDensity, CoareaNormalization.sharpReadout, Set.indicator_of_notMem hn]

theorem planeDensity_zero_outside_band {R : ℝ} (hR : 0 ≤ R) (Φ : FourMomenta → ℝ)
    {e : ℝ} (he : e ∉ Icc (-72*R^2) (72*R^2)) (p : PlaneParameters) :
    planeDensity R Φ e p = 0 := by
  have hn : planeShell p e ∉ CoareaNormalization.allFourFlags R :=
    fun hf => he (planeShell_flags_bounds hR p e hf).2
  simp [planeDensity, CoareaNormalization.sharpReadout, Set.indicator_of_notMem hn]

theorem planeDensity_bound {B R : ℝ} (hB : 0 ≤ B) (Φ : FourMomenta → ℝ)
    (hΦ : ∀ k ∈ CoareaNormalization.allFourFlags R, ‖Φ k‖ ≤ B) (e : ℝ) (p : PlaneParameters) :
    ‖planeDensity R Φ e p‖ ≤ B/2 := by
  by_cases hf : planeShell p e ∈ CoareaNormalization.allFourFlags R
  · rw [planeDensity, CoareaNormalization.sharpReadout, Set.indicator_of_mem hf, norm_mul]
    norm_num
    have hb : |Φ (planeShell p e)| ≤ B := hΦ (planeShell p e) hf
    linarith
  · simp only [planeDensity, CoareaNormalization.sharpReadout, Set.indicator_of_notMem hf, mul_zero, norm_zero]
    positivity

def planeEnergy (R : ℝ) (Φ : FourMomenta → ℝ) (e : ℝ) : ℝ :=
  ∫ p, planeDensity R Φ e p ∂planeTruncated R

theorem planeDensity_integrable {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k ∈ CoareaNormalization.allFourFlags R, ‖Φ k‖ ≤ B) (e : ℝ) :
    Integrable (planeDensity R Φ e) (planeTruncated R) := by
  letI := planeTruncated_finite hR
  have hm : Measurable (planeDensity R Φ e) :=
    (planeDensity_measurable R hΦm).comp (measurable_const.prodMk measurable_id)
  have hc : Integrable (fun _ : PlaneParameters => B/2) (planeTruncated R) := integrable_const _
  exact hc.mono' hm.aestronglyMeasurable (ae_of_all _ (planeDensity_bound hB Φ hΦ e))

theorem planeEnergy_measurable (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Measurable Φ) :
    Measurable (planeEnergy R Φ) :=
  (planeDensity_measurable R hΦ).stronglyMeasurable.integral_prod_right'.measurable

theorem planeEnergy_bound {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ)
    (hΦ : ∀ k ∈ CoareaNormalization.allFourFlags R, ‖Φ k‖ ≤ B) (e : ℝ) :
    ‖planeEnergy R Φ e‖ ≤ (B/2) * (planeTruncated R).real univ := by
  letI := planeTruncated_finite hR
  exact norm_integral_le_of_norm_le_const (ae_of_all _ (planeDensity_bound hB Φ hΦ e))

theorem planeEnergy_zero_outside_band {R : ℝ} (hR : 0 ≤ R) (Φ : FourMomenta → ℝ)
    {e : ℝ} (he : e ∉ Icc (-72*R^2) (72*R^2)) :
    planeEnergy R Φ e = 0 := by
  have hz : planeDensity R Φ e = 0 := funext (planeDensity_zero_outside_band hR Φ he)
  simp only [planeEnergy,hz,Pi.zero_apply,integral_zero]

theorem planeEnergy_integrable {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k ∈ CoareaNormalization.allFourFlags R, ‖Φ k‖ ≤ B) :
    Integrable (planeEnergy R Φ) := by
  let C := (B/2) * (planeTruncated R).real univ
  have hc : Integrable ((Icc (-72*R^2) (72*R^2)).indicator (fun _ : ℝ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const isCompact_Icc.measure_ne_top)
  apply hc.mono' (planeEnergy_measurable R hΦm).aestronglyMeasurable
  apply ae_of_all
  intro e
  by_cases he : e ∈ Icc (-72*R^2) (72*R^2)
  · simpa only [Set.indicator_of_mem he] using planeEnergy_bound hR hB Φ hΦ e
  · rw [Set.indicator_of_notMem he,planeEnergy_zero_outside_band hR Φ he,norm_zero]

def planeShift (b : Ray × E2) (i : Fin 4) : E :=
  ![0,(b.1.2:ℝ) • (b.1.1:E) + planePoint b.1.1 b.2,
    (b.1.2:ℝ) • (b.1.1:E),planePoint b.1.1 b.2] i

theorem planeShell_translate (k : E) (b : Ray × E2) (i : Fin 4) :
    planeShell (k,b) 0 i = k + planeShift b i := by
  fin_cases i <;>
    simp [planeShell,planeShift,rectangleFour,normalCoords_zero,planePoint_eq,add_assoc]

theorem planeBase_single_leg_null (i : Fin 4) {s : Set E} (hs : MeasurableSet s)
    (hzero : (volume : Measure E) s = 0) :
    planeBase ((fun p => planeShell p 0 i) ⁻¹' s) = 0 := by
  have hm : Measurable (fun p : PlaneParameters => planeShell p 0 i) :=
    (measurable_pi_apply i).comp
      (planeShell_joint_measurable.comp (measurable_const.prodMk measurable_id))
  have hset := hs.preimage hm
  rw [planeBase,Measure.prod_apply_symm hset]
  have hsection (b : Ray × E2) :
      (volume : Measure E) ((fun k : E => (k,b)) ⁻¹'
        ((fun p => planeShell p 0 i) ⁻¹' s)) = 0 := by
    have he : ((fun k : E => (k,b)) ⁻¹' ((fun p => planeShell p 0 i) ⁻¹' s)) =
        (fun k : E => k + planeShift b i) ⁻¹' s := by
      ext k
      simp only [mem_preimage,planeShell_translate]
    rw [he]
    simpa only [id_eq] using (((MeasurePreserving.id (volume : Measure E)).add_right
      (volume : Measure E) (planeShift b i)).measure_preimage hs.nullMeasurableSet).trans hzero
  simp_rw [hsection]
  simp

theorem plane_ae_faces_avoided (R : ℝ) :
    ∀ᵐ p ∂planeBase, ∀ i : Fin 4, ∀ j : Fin 3, |planeShell p 0 i j| ≠ R := by
  apply Filter.eventually_all.2
  intro i
  apply Filter.eventually_all.2
  intro j
  have hs : MeasurableSet {k : E | |k j| = R} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hz := planeBase_single_leg_null i hs (CoareaGlobal.euclidean_absolute_face_null j R)
  apply ae_iff.mpr
  simpa only [not_not] using hz

theorem planeSharp_continuousAt_zero (R : ℝ) {Φ : FourMomenta → ℝ}
    (hΦ : Continuous Φ) (p : PlaneParameters)
    (hp : ∀ i : Fin 4, ∀ j : Fin 3, |planeShell p 0 i j| ≠ R) :
    ContinuousAt (fun e => CoareaNormalization.sharpReadout R Φ (planeShell p e)) 0 := by
  have hc := planeShell_continuous p
  have hcoords : ∀ᶠ e in nhds (0:ℝ), ∀ i : Fin 4, ∀ j : Fin 3,
      (|planeShell p e i j| ≤ R ↔ |planeShell p 0 i j| ≤ R) := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro j
    have hout : Continuous (fun k : FourMomenta => |k i j|) := by fun_prop
    exact CoareaGlobal.eventually_le_iff_of_continuousAt
      (a := 0) (b := R) (hout.comp hc).continuousAt (hp i j)
  have hflags : ∀ᶠ e in nhds (0:ℝ),
      (planeShell p e ∈ CoareaNormalization.allFourFlags R ↔
       planeShell p 0 ∈ CoareaNormalization.allFourFlags R) := by
    filter_upwards [hcoords] with e he
    change (∀ i,∀ j,|planeShell p e i j| ≤ R) ↔ (∀ i,∀ j,|planeShell p 0 i j| ≤ R)
    exact forall_congr' fun i => forall_congr' fun j => he i j
  by_cases h0 : planeShell p 0 ∈ CoareaNormalization.allFourFlags R
  · have heq : (fun e => CoareaNormalization.sharpReadout R Φ (planeShell p e))
        =ᶠ[nhds 0] (fun e => Φ (planeShell p e)) := by
      filter_upwards [hflags] with e he
      exact Set.indicator_of_mem (he.mpr h0) Φ
    change Filter.Tendsto (fun e => CoareaNormalization.sharpReadout R Φ (planeShell p e))
      (nhds 0) (nhds (CoareaNormalization.sharpReadout R Φ (planeShell p 0)))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem h0]
    simpa only [Function.comp_def] using (hΦ.comp hc).continuousAt.tendsto.congr' heq.symm
  · have heq : (fun e => CoareaNormalization.sharpReadout R Φ (planeShell p e))
        =ᶠ[nhds 0] (fun _ => (0:ℝ)) := by
      filter_upwards [hflags] with e he
      exact Set.indicator_of_notMem (fun hh => h0 (he.mp hh)) Φ
    change Filter.Tendsto (fun e => CoareaNormalization.sharpReadout R Φ (planeShell p e))
      (nhds 0) (nhds (CoareaNormalization.sharpReadout R Φ (planeShell p 0)))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem h0]
    exact tendsto_const_nhds.congr' heq.symm

theorem planeDensity_continuousAt_zero_ae (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Continuous Φ) :
    ∀ᵐ p ∂planeBase, ContinuousAt (fun e => planeDensity R Φ e p) 0 := by
  filter_upwards [plane_ae_faces_avoided R] with p hp
  exact continuousAt_const.mul (planeSharp_continuousAt_zero R hΦ p hp)

theorem planeEnergy_continuousAt_zero {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦc : Continuous Φ)
    (hΦ : ∀ k ∈ CoareaNormalization.allFourFlags R, ‖Φ k‖ ≤ B) :
    ContinuousAt (planeEnergy R Φ) 0 := by
  letI := planeTruncated_finite hR
  have hi : Integrable (fun _ : PlaneParameters => B/2) (planeTruncated R) := integrable_const _
  have ha : ∀ᵐ p ∂planeTruncated R, ContinuousAt (fun e => planeDensity R Φ e p) 0 :=
    ae_restrict_of_ae (planeDensity_continuousAt_zero_ae R hΦc)
  change Filter.Tendsto (fun e => ∫ p,planeDensity R Φ e p ∂planeTruncated R)
    (nhds 0) (nhds (∫ p,planeDensity R Φ 0 p ∂planeTruncated R))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B/2)
  · exact Filter.Eventually.of_forall fun e =>
      (planeDensity_integrable hR hB Φ hΦc.measurable hΦ e).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun e => ae_of_all _ (planeDensity_bound hB Φ hΦ e)
  · exact hi
  · exact ha.mono fun _ hp => hp.tendsto

theorem plane_energy_peak_limit {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Φ : FourMomenta → ℝ) (hΦc : Continuous Φ)
    (hΦ : ∀ k ∈ CoareaNormalization.allFourFlags R, ‖Φ k‖ ≤ B) :
    Filter.Tendsto
      (fun c : ℝ => ∫ e, (c * CoareaNormalization.boxKernel (c*e)) * planeEnergy R Φ e)
      Filter.atTop (nhds (planeEnergy R Φ 0)) := by
  have ht := tendsto_integral_comp_smul_smul_of_integrable
    CoareaNormalization.boxKernel_nonneg CoareaNormalization.boxKernel_integral
    (by simpa using CoareaNormalization.boxKernel_tail)
    (planeEnergy_integrable hR hB Φ hΦc.measurable hΦ)
    (planeEnergy_continuousAt_zero hR hB Φ hΦc hΦ)
  simpa [smul_eq_mul] using ht

/-- Before eliminating normal energy, the same parameters carry r² dr. -/
def planeNormalBase : Measure PlaneParameters :=
  (volume : Measure E).prod (rayMeasure.prod (volume : Measure E2))
instance : SigmaFinite planeNormalBase := by unfold planeNormalBase; infer_instance

theorem radial_two_from_one :
    Measure.volumeIoiPow 2 = radialOne.withDensity (fun r : Radius => ENNReal.ofReal (r:ℝ)) := by
  unfold radialOne Measure.volumeIoiPow
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext r
  simp only [Pi.mul_apply,pow_one]
  have hr : 0 ≤ (r:ℝ) := le_of_lt r.property
  rw [← ENNReal.ofReal_mul hr]
  congr 1
  ring

theorem normalBase_from_planeBase :
    planeNormalBase = planeBase.withDensity
      (fun p : PlaneParameters => ENNReal.ofReal (p.2.1.2:ℝ)) := by
  have hray : rayMeasure = rayOne.withDensity (fun q : Ray => ENNReal.ofReal (q.2:ℝ)) := by
    rw [rayMeasure,radial_two_from_one,prod_withDensity_right (by fun_prop)]
    rfl
  rw [planeNormalBase,hray,prod_withDensity_left (by fun_prop),
    prod_withDensity_right (by fun_prop)]
  rfl

theorem twice_normalBase :
    planeBase.withDensity (fun p : PlaneParameters => ENNReal.ofReal (2*(p.2.1.2:ℝ))) =
      (2:ℝ≥0∞) • planeNormalBase := by
  rw [normalBase_from_planeBase,← withDensity_smul _ (by fun_prop)]
  congr 1
  funext p
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  norm_num

def normalScale (p : PlaneParameters × ℝ) : PlaneParameters × ℝ :=
  (p.1,p.2/(2*(p.1.2.1.2:ℝ)))

theorem normalScale_measurable : Measurable normalScale := by unfold normalScale; fun_prop

theorem normal_scale_volume {r : ℝ} (hr : 0<r) :
    Measure.map (fun e : ℝ => e/(2*r)) volume =
      ENNReal.ofReal (2*r) • (volume : Measure ℝ) := by
  have hz : (2*r)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have hh := Measure.map_addHaar_smul (volume : Measure ℝ) hz
  have hpos : 0 < r*2 := by positivity
  simpa only [smul_eq_mul,Module.finrank_self,pow_one,inv_inv,
    div_eq_mul_inv,mul_comm,abs_of_pos hpos] using hh

/-- The Jacobian is proved on arbitrary measurable subsets of the complete parameter product. -/
theorem normalScale_map :
    Measure.map normalScale (planeBase.prod (volume : Measure ℝ)) =
      (planeBase.withDensity (fun p => ENNReal.ofReal (2*(p.2.1.2:ℝ)))).prod volume := by
  ext s hs
  rw [Measure.map_apply normalScale_measurable hs,
    Measure.prod_apply (hs.preimage normalScale_measurable),Measure.prod_apply hs,
    lintegral_withDensity_eq_lintegral_mul planeBase (by fun_prop)
      (measurable_measure_prodMk_left hs)]
  apply lintegral_congr_ae
  apply ae_of_all
  intro p
  have hsection : MeasurableSet ((Prod.mk p) ⁻¹' s) := hs.preimage measurable_prodMk_left
  have hr : 0 < (p.2.1.2:ℝ) := p.2.1.2.property
  have hm := Measure.map_apply (μ := (volume : Measure ℝ)) (by fun_prop : Measurable
    (fun e : ℝ => e/(2*(p.2.1.2:ℝ)))) hsection
  rw [normal_scale_volume hr,Measure.smul_apply] at hm
  simpa only [normalScale,Set.preimage_preimage,Pi.mul_apply,smul_eq_mul] using hm.symm

def energyInputMeasure : Measure (PlaneParameters × ℝ) :=
  (1/2:ℝ≥0∞) • planeBase.prod (volume : Measure ℝ)

theorem normalScale_preserving :
    MeasurePreserving normalScale energyInputMeasure (planeNormalBase.prod (volume : Measure ℝ)) := by
  refine ⟨normalScale_measurable,?_⟩
  rw [energyInputMeasure,Measure.map_smul,normalScale_map,twice_normalBase,Measure.prod_smul_left,
    smul_smul]
  norm_num only [one_div]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_smul]

def normalShuffle : (PlaneParameters × ℝ) ≃ᵐ NormalInput :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl E)
      (MeasurableEquiv.prodAssoc.trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ray) MeasurableEquiv.prodComm)))

theorem normalShuffle_preserving :
    MeasurePreserving normalShuffle (planeNormalBase.prod (volume : Measure ℝ))
      normalInputMeasure := by
  exact (measurePreserving_prodAssoc (volume : Measure E)
    (rayMeasure.prod (volume : Measure E2)) (volume : Measure ℝ)).trans
      ((MeasurePreserving.id (volume : Measure E)).prod
        ((measurePreserving_prodAssoc rayMeasure (volume : Measure E2) (volume : Measure ℝ)).trans
          ((MeasurePreserving.id rayMeasure).prod Measure.measurePreserving_swap)))

def energyToTriple (q : PlaneParameters × ℝ) : E × (E × E) :=
  fullNormal (normalShuffle (normalScale q))

theorem energyToTriple_preserving :
    MeasurePreserving energyToTriple energyInputMeasure
      ((volume : Measure E).prod (volume.prod volume)) :=
  fullNormal_preserving.comp (normalShuffle_preserving.comp normalScale_preserving)

theorem energyToTriple_quartet (p : PlaneParameters) (e : ℝ) :
    rectangleFour (energyToTriple (p,e)).1 (energyToTriple (p,e)).2.1
      (energyToTriple (p,e)).2.2 = planeShell p e := rfl

theorem planeEnergy_full_integral {R : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (e : ℝ) :
    planeEnergy R Φ e = ∫ p, planeDensity R Φ e p ∂planeBase :=
  setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun _ hp => planeDensity_zero_outside_box hR Φ e hp)

theorem full_plane_weighted_joint_integrable {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k∈CoareaNormalization.allFourFlags R, ‖Φ k‖≤B) (c : ℝ) :
    Integrable (fun x : ℝ × PlaneParameters =>
      CoareaGlobal.layerKernel c x.1 * planeDensity R Φ x.1 x.2)
      ((volume : Measure ℝ).prod planeBase) := by
  have ht : Integrable ((Icc (-72*R^2) (72*R^2)).indicator (fun _ : ℝ => |c|/2)) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const isCompact_Icc.measure_ne_top)
  have hp : Integrable ((planeBox R).indicator (fun _ : PlaneParameters => B/2)) planeBase :=
    (integrable_indicator_iff (planeBox_measurable R)).2
      (integrableOn_const (planeBox_finite hR).ne)
  have hm : Measurable (fun x : ℝ × PlaneParameters =>
      CoareaGlobal.layerKernel c x.1 * planeDensity R Φ x.1 x.2) :=
    ((CoareaGlobal.layerKernel_measurable c).comp measurable_fst).mul (planeDensity_measurable R hΦm)
  apply (ht.mul_prod hp).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  by_cases he : x.1∈Icc (-72*R^2) (72*R^2)
  · rw [Set.indicator_of_mem he]
    by_cases hp : x.2∈planeBox R
    · rw [Set.indicator_of_mem hp,norm_mul]
      exact mul_le_mul (CoareaGlobal.layerKernel_norm_bound c x.1)
        (planeDensity_bound hB Φ hΦ x.1 x.2) (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hp,planeDensity_zero_outside_box hR Φ x.1 hp,
        mul_zero,mul_zero,norm_zero]
  · rw [Set.indicator_of_notMem he,planeDensity_zero_outside_band hR Φ he x.2,
      zero_mul,mul_zero,norm_zero]

theorem full_plane_fubini {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k∈CoareaNormalization.allFourFlags R, ‖Φ k‖≤B) (c : ℝ) :
    (∫ q : PlaneParameters × ℝ,
      CoareaGlobal.layerKernel c q.2 * planeDensity R Φ q.2 q.1 ∂(planeBase.prod volume)) =
      ∫ e, CoareaGlobal.layerKernel c e * planeEnergy R Φ e := by
  have hj := full_plane_weighted_joint_integrable hR hB Φ hΦm hΦ c
  have hs := integral_prod_symm _ hj.swap
  simp only [Function.comp_def,Prod.swap] at hs
  rw [hs]
  apply integral_congr_ae
  apply ae_of_all
  intro e
  dsimp only
  rw [planeEnergy_full_integral hR Φ e,integral_const_mul]

/-- The same original Cartesian sharp layer equals the full, integrable normal-energy density. -/
theorem original_layer_eq_planeEnergy {R : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) (c : ℝ) :
    (∫ z : CoareaNormalization.Nine,
      PolarCoordinates.sharpLayer R c Φ (CoareaNormalization.physicalFour z)) =
      ∫ e, CoareaGlobal.layerKernel c e * planeEnergy R Φ e := by
  let F : E × (E × E) → ℝ :=
    fun t => PolarCoordinates.sharpLayer R c Φ (rectangleFour t.1 t.2.1 t.2.2)
  have hF : Integrable F ((volume : Measure E).prod (volume.prod volume)) :=
    original_triple_rectangular_integrable hR c Φ hΦ
  have hn := integral_map PolarCoordinates.nineToTriple_preserves_volume.measurable.aemeasurable
    (PolarCoordinates.nineToTriple_preserves_volume.map_eq.symm ▸ hF.aestronglyMeasurable)
  rw [PolarCoordinates.nineToTriple_preserves_volume.map_eq] at hn
  have he := integral_map energyToTriple_preserving.measurable.aemeasurable
    (energyToTriple_preserving.map_eq.symm ▸ hF.aestronglyMeasurable)
  rw [energyToTriple_preserving.map_eq] at he
  have hr := RectangularCoordinates.rectangle_integral (PolarCoordinates.sharpLayer R c Φ)
    (PolarCoordinates.original_sharp_layer_integrable hR c Φ hΦ).aestronglyMeasurable
  have hn' :
      (∫ z : CoareaNormalization.Nine,
        PolarCoordinates.sharpLayer R c Φ (RectangularCoordinates.rectangle z)) = ∫ t,F t := by
    simpa only [F,PolarCoordinates.nineToTriple,rectangleFour_nine] using hn.symm
  have he' : (∫ t,F t) = ∫ q : PlaneParameters × ℝ,
      PolarCoordinates.sharpLayer R c Φ (planeShell q.1 q.2) ∂energyInputMeasure := by
    simpa only [F,energyToTriple_quartet] using he
  rw [hr,hn',he',energyInputMeasure,integral_smul_measure]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  rw [← full_plane_fubini hR hB Φ hΦ.measurable hbound c,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  simp only [PolarCoordinates.sharpLayer,planeShell_energy,planeDensity,CoareaGlobal.layerKernel]
  ring

theorem original_plane_energy_limit {R : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Filter.Tendsto
      (fun c : ℝ => ∫ z : CoareaNormalization.Nine,
        PolarCoordinates.sharpLayer R c Φ (CoareaNormalization.physicalFour z))
      Filter.atTop (nhds (planeEnergy R Φ 0)) := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  have ht := plane_energy_peak_limit hR hB Φ hΦ hbound
  simpa only [original_layer_eq_planeEnergy hR Φ hΦ,CoareaGlobal.layerKernel] using ht

/-- Equality of the full pairing integral with the independently constructed plane-area integral. -/
theorem pairing_eq_plane_integral {R : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    (∫ k, Φ k ∂(ResonantMeasure.pairingMeasure R)) =
      (1/2:ℝ) * ∫ p, CoareaNormalization.sharpReadout R Φ (planeShell p 0) ∂planeBase := by
  have he := tendsto_nhds_unique (CoareaGlobal.original_sharp_coarea_limit hR Φ hΦ)
    (original_plane_energy_limit hR Φ hΦ)
  rw [he,planeEnergy_full_integral hR Φ 0]
  exact integral_const_mul _ _

def unitVector (x : E) : E := if x=0 then e0 else ‖x‖⁻¹ • x

theorem unitVector_norm (x : E) : ‖unitVector x‖ = 1 := by
  by_cases hx : x=0
  · simp [unitVector,hx]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp [unitVector,hx,norm_smul,hn]

def direction (x : E) : Sphere := ⟨unitVector x, by
  change dist (unitVector x) 0 = 1
  simpa [dist_zero_right] using unitVector_norm x⟩

theorem unitVector_measurable : Measurable unitVector := by
  unfold unitVector
  exact Measurable.ite (measurableSet_singleton (0:E)) measurable_const
    ((measurable_norm.inv).smul measurable_id)

theorem direction_measurable : Measurable direction :=
  unitVector_measurable.subtype_mk

theorem direction_polar (σ : Sphere) (r : Radius) :
    direction ((r:ℝ) • (σ:E)) = σ := by
  have hr : 0 < (r:ℝ) := r.property
  have hnorm : ‖(r:ℝ) • (σ:E)‖ = (r:ℝ) := by simp [norm_smul,abs_of_pos hr]
  have hx : (r:ℝ) • (σ:E) ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ hr)
  apply Subtype.ext
  change unitVector ((r:ℝ) • (σ:E)) = (σ:E)
  rw [unitVector,if_neg hx,hnorm,smul_smul]
  simp [ne_of_gt hr]

theorem direction_representation {x : E} (hx : x≠0) :
    ‖x‖ • (direction x : E) = x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  change ‖x‖ • unitVector x = x
  rw [unitVector,if_neg hx,smul_smul]
  simp [hn]

def hyperplaneArea (x : E) : Measure E :=
  (Measure.euclideanHausdorffMeasure 2).restrict {y | inner ℝ x y = 0}

theorem hyperplaneArea_direction {x : E} (hx : x≠0) :
    hyperplaneArea x = planeArea (direction x) := by
  unfold hyperplaneArea planeArea
  congr 1
  ext y
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  change (inner ℝ x y=0) ↔ (inner ℝ (direction x:E) y=0)
  nth_rw 1 [← direction_representation hx]
  rw [real_inner_smul_left,mul_eq_zero]
  simp [hn]

def physicalPlaneReading (R : ℝ) (Φ : FourMomenta → ℝ) (k x : E) : ℝ :=
  (2*‖x‖)⁻¹ * ∫ z : E2,
    CoareaNormalization.sharpReadout R Φ (rectangleFour k x (planePoint (direction x) z))

theorem physicalPlaneReading_measurable (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Measurable Φ) :
    Measurable (Function.uncurry (physicalPlaneReading R Φ)) := by
  have hd : Measurable (fun p : (E × E) × E2 => (direction p.1.2,p.2)) :=
    (direction_measurable.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hp := plane_joint_measurable.comp hd
  have hm : Measurable (fun p : (E × E) × E2 =>
      (p.1.1,(p.1.2,planePoint (direction p.1.2) p.2))) := by
    exact (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (by simpa only [Function.comp_def] using hp))
  have hf := (CoareaNormalization.sharpReadout_measurable R hΦ).comp
    (rectangleFour_continuous.measurable.comp hm)
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E2))).measurable
  have hi' : Measurable (fun p : E × E => ∫ z : E2,
      CoareaNormalization.sharpReadout R Φ (rectangleFour p.1 p.2 (planePoint (direction p.2) z))) := by
    simpa only [Function.comp_def] using hi
  exact (by fun_prop : Measurable (fun p : E×E => (2*‖p.2‖)⁻¹)).mul hi'

theorem physicalPlaneReading_area (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Measurable Φ)
    (k x : E) :
    physicalPlaneReading R Φ k x =
      (2*‖x‖)⁻¹ * ∫ y : E,
        CoareaNormalization.sharpReadout R Φ (rectangleFour k x y) ∂hyperplaneArea x := by
  by_cases hx : x=0
  · simp [physicalPlaneReading,hx]
  · rw [hyperplaneArea_direction hx]
    have hf : Measurable (fun y : E => CoareaNormalization.sharpReadout R Φ (rectangleFour k x y)) :=
      (CoareaNormalization.sharpReadout_measurable R hΦ).comp
        (rectangleFour_continuous.measurable.comp (measurable_const.prodMk
          (measurable_const.prodMk measurable_id)))
    have hi := integral_map (planeArea_preserving (direction x)).measurable.aemeasurable
      ((planeArea_preserving (direction x)).map_eq.symm ▸
        (hf.aestronglyMeasurable (μ := planeArea (direction x))))
    rw [(planeArea_preserving (direction x)).map_eq] at hi
    unfold physicalPlaneReading
    congr 1
    simpa only [planePoint_eq] using hi.symm

theorem physicalPlaneReading_ray (R : ℝ) (Φ : FourMomenta → ℝ) (k : E) (p : Ray) :
    physicalPlaneReading R Φ k (PolarCoordinates.polarVector p) =
      (2*(p.2:ℝ))⁻¹ * ∫ z : E2,
        CoareaNormalization.sharpReadout R Φ (planeShell (k,(p,z)) 0) := by
  have hr : 0 < (p.2:ℝ) := p.2.property
  have hn : ‖PolarCoordinates.polarVector p‖ = (p.2:ℝ) := by
    simp [PolarCoordinates.polarVector,norm_smul,abs_of_pos hr]
  rw [physicalPlaneReading,hn]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [PolarCoordinates.polarVector,direction_polar,planeShell,zero_div,normalCoords_zero,
    planePoint_eq]

theorem rayMeasure_from_rayOne :
    rayMeasure = rayOne.withDensity (fun p : Ray => ENNReal.ofReal (p.2:ℝ)) := by
  rw [rayMeasure,radial_two_from_one,prod_withDensity_right (by fun_prop)]
  rfl

theorem ray_integral_reading (R : ℝ) {Φ : FourMomenta → ℝ} (hΦ : Measurable Φ) (k : E) :
    (∫ x : E, physicalPlaneReading R Φ k x) =
      (1/2:ℝ) * ∫ p : Ray, (∫ z : E2,
        CoareaNormalization.sharpReadout R Φ (planeShell (k,(p,z)) 0)) ∂rayOne := by
  have hmk : Measurable (fun x : E => (k,x)) := measurable_const.prodMk measurable_id
  have hh := (physicalPlaneReading_measurable R hΦ).comp hmk
  have hm : Measurable (physicalPlaneReading R Φ k) := by
    simpa only [Function.comp_def,Function.uncurry] using hh
  rw [PolarCoordinates.polarVector_integral _ hm.aestronglyMeasurable]
  change (∫ p : Ray, physicalPlaneReading R Φ k (PolarCoordinates.polarVector p) ∂rayMeasure) = _
  rw [rayMeasure_from_rayOne,integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [ENNReal.toReal_ofReal p.2.property.le,smul_eq_mul,physicalPlaneReading_ray]
  have hr : (p.2:ℝ) ≠ 0 := ne_of_gt p.2.property
  field_simp

theorem planeDensity_full_integrable {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ k∈CoareaNormalization.allFourFlags R, ‖Φ k‖≤B) (e : ℝ) :
    Integrable (planeDensity R Φ e) planeBase := by
  have hp : Integrable ((planeBox R).indicator (fun _ : PlaneParameters => B/2)) planeBase :=
    (integrable_indicator_iff (planeBox_measurable R)).2
      (integrableOn_const (planeBox_finite hR).ne)
  have hm : Measurable (planeDensity R Φ e) :=
    (planeDensity_measurable R hΦm).comp (measurable_const.prodMk measurable_id)
  apply hp.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro p
  by_cases hp : p∈planeBox R
  · rw [Set.indicator_of_mem hp]
    exact planeDensity_bound hB Φ hΦ e p
  · rw [Set.indicator_of_notMem hp,planeDensity_zero_outside_box hR Φ e hp,norm_zero]

theorem pairing_eq_physical_reading {R : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    (∫ k, Φ k ∂(ResonantMeasure.pairingMeasure R)) =
      ∫ k : E, ∫ x : E, physicalPlaneReading R Φ k x := by
  have he := tendsto_nhds_unique (CoareaGlobal.original_sharp_coarea_limit hR Φ hΦ)
    (original_plane_energy_limit hR Φ hΦ)
  rw [he,planeEnergy_full_integral hR Φ 0]
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  have hi := planeDensity_full_integrable hR hB Φ hΦ.measurable hbound 0
  change Integrable (fun p : E × (Ray × E2) => planeDensity R Φ 0 p)
    ((volume : Measure E).prod (rayOne.prod (volume : Measure E2))) at hi
  rw [planeBase,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with k hk
  rw [ray_integral_reading R hΦ.measurable k, integral_prod _ hk,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  exact integral_const_mul _ _

/-- The full original four-leg coarea formula, with physical dk dx and normalized
Hausdorff area on x⊥. The single exceptional vector x=0 is not an assumed exclusion. -/
theorem pairing_full_plane_coarea {R : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    (∫ k, Φ k ∂(ResonantMeasure.pairingMeasure R)) =
      ∫ k : E, ∫ x : E, (2*‖x‖)⁻¹ *
        ∫ y : E, CoareaNormalization.sharpReadout R Φ (rectangleFour k x y)
          ∂((Measure.euclideanHausdorffMeasure 2).restrict {y : E | inner ℝ x y=0}) := by
  rw [pairing_eq_physical_reading hR Φ hΦ]
  apply integral_congr_ae
  apply ae_of_all
  intro k
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact physicalPlaneReading_area R hΦ.measurable k x

/-- Independent complete plane construction, using r dr and actual orthonormal plane area. -/
def planeAllowed (R : ℝ) : Set PlaneParameters :=
  {p | planeShell p 0 ∈ CoareaNormalization.allFourFlags R}

def planeParameterMeasure (R : ℝ) : Measure PlaneParameters :=
  (1/2:ℝ≥0∞) • planeBase.restrict (planeAllowed R)

def planeMeasure (R : ℝ) : Measure FourMomenta :=
  Measure.map (fun p => planeShell p 0) (planeParameterMeasure R)

theorem planeShell_zero_measurable : Measurable (fun p : PlaneParameters => planeShell p 0) :=
  planeShell_joint_measurable.comp (measurable_const.prodMk measurable_id)

theorem planeAllowed_measurable (R : ℝ) : MeasurableSet (planeAllowed R) :=
  (CoareaNormalization.allFourFlags_measurable R).preimage planeShell_zero_measurable

theorem planeParameterMeasure_finite {R : ℝ} (hR : 0≤R) :
    IsFiniteMeasure (planeParameterMeasure R) := by
  constructor
  simp only [planeParameterMeasure,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  apply ENNReal.mul_lt_top (by norm_num)
  apply lt_of_le_of_lt (measure_mono (show planeAllowed R ⊆ planeBox R from
    fun p hp => (planeShell_flags_bounds hR p 0 hp).1))
  exact planeBox_finite hR

theorem planeMeasure_finite {R : ℝ} (hR : 0≤R) :
    IsFiniteMeasure (planeMeasure R) := by
  letI := planeParameterMeasure_finite hR
  unfold planeMeasure
  infer_instance

theorem planeMeasure_integral (R : ℝ) (Φ : FourMomenta → ℝ) (hΦ : Measurable Φ) :
    (∫ k, Φ k ∂planeMeasure R) =
      (1/2:ℝ) * ∫ p, CoareaNormalization.sharpReadout R Φ (planeShell p 0) ∂planeBase := by
  rw [planeMeasure,integral_map planeShell_zero_measurable.aemeasurable hΦ.aestronglyMeasurable,
    planeParameterMeasure,integral_smul_measure]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  congr 1
  rw [← integral_indicator (planeAllowed_measurable R)]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  by_cases hp : p∈planeAllowed R
  · rw [Set.indicator_of_mem hp]
    exact (Set.indicator_of_mem
      (show planeShell p 0 ∈ CoareaNormalization.allFourFlags R from hp) Φ).symm
  · rw [Set.indicator_of_notMem hp]
    exact (Set.indicator_of_notMem
      (show planeShell p 0 ∉ CoareaNormalization.allFourFlags R from hp) Φ).symm

/-- The concrete plane measure and the concrete global pairing measure are equal on all Borel sets. -/
theorem planeMeasure_eq_pairingMeasure {R : ℝ} (hR : 0≤R) :
    planeMeasure R = ResonantMeasure.pairingMeasure R := by
  letI := planeMeasure_finite hR
  letI := ResonantMeasure.pairingMeasure_finite hR
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [planeMeasure_integral R f f.continuous.measurable]
  exact (pairing_eq_plane_integral hR f f.continuous).symm

/-! Complete declaration types and axiom audit. -/
#check planeBox_measurable
#print axioms planeBox_measurable
#check planeBox_finite
#print axioms planeBox_finite
#check planeTruncated_finite
#print axioms planeTruncated_finite
#check planeShell_energy
#print axioms planeShell_energy
#check planeShell_joint_measurable
#print axioms planeShell_joint_measurable
#check planeShell_continuous
#print axioms planeShell_continuous
#check rectangle_flags_bounds
#print axioms rectangle_flags_bounds
#check planeShell_flags_bounds
#print axioms planeShell_flags_bounds
#check planeDensity_measurable
#print axioms planeDensity_measurable
#check planeDensity_zero_outside_box
#print axioms planeDensity_zero_outside_box
#check planeDensity_zero_outside_band
#print axioms planeDensity_zero_outside_band
#check planeDensity_bound
#print axioms planeDensity_bound
#check planeDensity_integrable
#print axioms planeDensity_integrable
#check planeEnergy_measurable
#print axioms planeEnergy_measurable
#check planeEnergy_bound
#print axioms planeEnergy_bound
#check planeEnergy_zero_outside_band
#print axioms planeEnergy_zero_outside_band
#check planeEnergy_integrable
#print axioms planeEnergy_integrable
#check planeShell_translate
#print axioms planeShell_translate
#check planeBase_single_leg_null
#print axioms planeBase_single_leg_null
#check plane_ae_faces_avoided
#print axioms plane_ae_faces_avoided
#check planeSharp_continuousAt_zero
#print axioms planeSharp_continuousAt_zero
#check planeDensity_continuousAt_zero_ae
#print axioms planeDensity_continuousAt_zero_ae
#check planeEnergy_continuousAt_zero
#print axioms planeEnergy_continuousAt_zero
#check plane_energy_peak_limit
#print axioms plane_energy_peak_limit
#check radial_two_from_one
#print axioms radial_two_from_one
#check normalBase_from_planeBase
#print axioms normalBase_from_planeBase
#check twice_normalBase
#print axioms twice_normalBase
#check normalScale_measurable
#print axioms normalScale_measurable
#check normal_scale_volume
#print axioms normal_scale_volume
#check normalScale_map
#print axioms normalScale_map
#check normalScale_preserving
#print axioms normalScale_preserving
#check normalShuffle_preserving
#print axioms normalShuffle_preserving
#check energyToTriple_preserving
#print axioms energyToTriple_preserving
#check energyToTriple_quartet
#print axioms energyToTriple_quartet
#check planeEnergy_full_integral
#print axioms planeEnergy_full_integral
#check full_plane_weighted_joint_integrable
#print axioms full_plane_weighted_joint_integrable
#check full_plane_fubini
#print axioms full_plane_fubini
#check original_layer_eq_planeEnergy
#print axioms original_layer_eq_planeEnergy
#check original_plane_energy_limit
#print axioms original_plane_energy_limit
#check pairing_eq_plane_integral
#print axioms pairing_eq_plane_integral
#check unitVector_norm
#print axioms unitVector_norm
#check unitVector_measurable
#print axioms unitVector_measurable
#check direction_measurable
#print axioms direction_measurable
#check direction_polar
#print axioms direction_polar
#check direction_representation
#print axioms direction_representation
#check hyperplaneArea_direction
#print axioms hyperplaneArea_direction
#check physicalPlaneReading_measurable
#print axioms physicalPlaneReading_measurable
#check physicalPlaneReading_area
#print axioms physicalPlaneReading_area
#check physicalPlaneReading_ray
#print axioms physicalPlaneReading_ray
#check rayMeasure_from_rayOne
#print axioms rayMeasure_from_rayOne
#check ray_integral_reading
#print axioms ray_integral_reading
#check planeDensity_full_integrable
#print axioms planeDensity_full_integrable
#check pairing_eq_physical_reading
#print axioms pairing_eq_physical_reading
#check pairing_full_plane_coarea
#print axioms pairing_full_plane_coarea
#check planeShell_zero_measurable
#print axioms planeShell_zero_measurable
#check planeAllowed_measurable
#print axioms planeAllowed_measurable
#check planeParameterMeasure_finite
#print axioms planeParameterMeasure_finite
#check planeMeasure_finite
#print axioms planeMeasure_finite
#check planeMeasure_integral
#print axioms planeMeasure_integral
#check planeMeasure_eq_pairingMeasure
#print axioms planeMeasure_eq_pairingMeasure

end
end Resonance.PlaneGlobal
