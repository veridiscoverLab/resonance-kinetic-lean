import Resonance.CriticalLogShells
import Resonance.CornerLayerVolume
import Resonance.CollisionFrequencyCompactCore

/-! The actual reference inverse frequency on the original cube,
including the critical exponent 3/2. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CornerInverseFrequency
noncomputable section
set_option maxHeartbeats 800000
open Resonance.PlaneCoarea Resonance.CornerFrequencyBounds
open Resonance.CubeFrequencyReflection Resonance.CollisionFrequency
open Resonance.CollisionFrequencyCompactCore Resonance.CornerLayerVolume
open Resonance.CriticalLogShells Resonance.FiberContinuity

theorem cornerDepth_continuous (R:ℝ) : Continuous (cornerDepth R) := by
  unfold cornerDepth maxDeficit cornerCoordinates
  fun_prop

theorem cornerDepth_eq_radius_div {R:ℝ} (hR:0<R) (k:E) :
    cornerDepth R k=cornerRadius R k/(2*R) := by
  unfold cornerDepth maxDeficit cornerCoordinates cornerRadius
  rw [max_div_div_right (by positivity),max_div_div_right (by positivity)]

theorem corner_of_nonpositive_depth {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) (he:cornerDepth R k≤0) : isCubeCorner R k := by
  intro i
  have hi : cornerCoordinates R k i=0 := le_antisymm
    ((le_maxDeficit _ i).trans he) (cornerCoordinates_bounds hR k hk i).1
  unfold cornerCoordinates at hi
  have hn : R-|k i|=0 := (div_eq_zero_iff.mp hi).resolve_right (by positivity)
  linarith

theorem reference_inverse_critical_lintegral {R:ℝ} (hR:0<R) :
    (∫⁻k in ResonantMeasure.cube R,
      ENNReal.ofReal ((referenceFrequency R k)^(-(3:ℝ)/2)))<∞ := by
  let μ : Measure E := volume.restrict (ResonantMeasure.cube R)
  have hcube : MeasurableSet (ResonantMeasure.cube R) := (cube_isCompact R).measurableSet
  have hμ : μ univ<∞ := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ]
    exact (cube_isCompact R).measure_lt_top
  have hsmall := small_layer_critical_integral_finite μ (cornerDepth R) (referenceFrequency R)
    (cornerDepth_continuous R).measurable (referenceLower_pos hR)
    (show 0≤8*(2*R)^3 by positivity)
    (fun r hr _hrsmall=>by
      have hs : μ {k|0<cornerDepth R k ∧ cornerDepth R k≤r}≤
          volume {k∈ResonantMeasure.cube R|cornerDepth R k≤r} := by
        have hm : MeasurableSet {k:E|0<cornerDepth R k ∧ cornerDepth R k≤r} :=
          (measurableSet_lt measurable_const (cornerDepth_continuous R).measurable).inter
            (measurableSet_le (cornerDepth_continuous R).measurable measurable_const)
        dsimp [μ]
        rw [Measure.restrict_apply hm]
        exact measure_mono (fun k hk=>⟨hk.2,hk.1.2⟩)
      apply (hs.trans (cornerDepth_layer_volume_le hR r)).trans_eq
      rw [←ENNReal.ofReal_pow (by positivity),show (8:ℝ≥0∞)=ENNReal.ofReal (8:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤8)]
      congr 1
      ring)
    (by
      filter_upwards [ae_restrict_mem hcube] with k hk hksmall
      exact (referenceFrequency_corner_scale hR hk hksmall.1
        (hksmall.2.trans exp_cutoff_le)).1)
  obtain ⟨m,hm,hcore⟩ := referenceFrequency_compactCore_lower hR
    (show 0<2*R*Real.exp (-8) by positivity)
  have hsmeas : MeasurableSet (smallLayer (cornerDepth R)) := by
    unfold smallLayer
    exact (measurableSet_lt measurable_const (cornerDepth_continuous R).measurable).inter
      (measurableSet_le (cornerDepth_continuous R).measurable measurable_const)
  have hout : (∫⁻k in (smallLayer (cornerDepth R))ᶜ,
      ENNReal.ofReal ((referenceFrequency R k)^(-(3:ℝ)/2)) ∂μ)<∞ := by
    have hp : ∀ᵐk∂μ.restrict (smallLayer (cornerDepth R))ᶜ,
        ENNReal.ofReal ((referenceFrequency R k)^(-(3:ℝ)/2))≤ENNReal.ofReal (m^(-(3:ℝ)/2)) := by
      filter_upwards [ae_restrict_mem hsmeas.compl,ae_restrict_of_ae (ae_restrict_mem hcube)] with k hk hkc
      by_cases he:0<cornerDepth R k
      · have he1 : Real.exp (-8)<cornerDepth R k := by
          by_contra h
          exact hk ⟨he,le_of_not_gt h⟩
        have hr : 2*R*Real.exp (-8)≤cornerRadius R k := by
          rw [cornerDepth_eq_radius_div hR] at he1
          exact (show 2*R*Real.exp (-8)=Real.exp (-8)*(2*R) by ring).le.trans
            ((le_div_iff₀ (by positivity)).mp he1.le)
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_nonpos hm (hcore k hkc hr) (by norm_num))
      · rw [referenceFrequency_corner_zero (corner_of_nonpositive_depth hR hkc (le_of_not_gt he)),
          Real.zero_rpow (by norm_num:-(3:ℝ)/2≠0)]
        simp
    apply lt_of_le_of_lt (lintegral_mono_ae hp)
    rw [lintegral_const,Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (measure_mono (subset_univ _)) hμ)
  change (∫⁻k,ENNReal.ofReal ((referenceFrequency R k)^(-(3:ℝ)/2)) ∂μ)<∞
  rw [←lintegral_add_compl _ hsmeas]
  exact ENNReal.add_lt_top.mpr ⟨hsmall,hout⟩

theorem reference_inverse_critical_integrable {R:ℝ} (hR:0<R) :
    IntegrableOn (fun k=> (referenceFrequency R k)^(-(3:ℝ)/2))
      (ResonantMeasure.cube R) := by
  have hm : AEMeasurable (referenceFrequency R)
      (volume.restrict (ResonantMeasure.cube R)) :=
    (referenceFrequency_continuousOn hR.le).aemeasurable (cube_isCompact R).measurableSet
  refine ⟨(hm.pow_const (-(3:ℝ)/2)).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hp (k:E) : 0≤(referenceFrequency R k)^(-(3:ℝ)/2) :=
    Real.rpow_nonneg (by
      unfold referenceFrequency lossFrequency
      apply mul_nonneg (inv_nonneg.mpr (referenceProfile_positive k).le)
      apply integral_nonneg
      intro q
      exact mul_nonneg (mul_nonneg (referenceProfile_positive _).le (referenceProfile_positive _).le)
        (referenceProfile_positive _).le) _
  simp only [Real.norm_eq_abs,abs_of_nonneg (hp _)]
  exact reference_inverse_critical_lintegral hR

theorem referenceFrequency_positive_ae {R:ℝ} (hR:0<R) :
    ∀ᵐk∂(volume:Measure E).restrict (ResonantMeasure.cube R),0<referenceFrequency R k := by
  have hcube := (cube_isCompact R).measurableSet
  have hz : (volume.restrict (ResonantMeasure.cube R)) {k:E|cornerDepth R k=0}=0 := by
    rw [Measure.restrict_apply
      (show MeasurableSet {k:E|cornerDepth R k=0} from
        measurableSet_eq_fun (cornerDepth_continuous R).measurable measurable_const)]
    have he : {k:E|cornerDepth R k=0}∩ResonantMeasure.cube R=
        {k∈ResonantMeasure.cube R|cornerDepth R k=0} := by ext k; exact and_comm
    rw [he]
    exact cornerDepth_zero_volume hR
  have he : ∀ᵐk∂(volume:Measure E).restrict (ResonantMeasure.cube R),cornerDepth R k≠0 := by
    simpa only [ae_iff,not_not] using hz
  filter_upwards [ae_restrict_mem hcube,he] with k hk he
  apply Resonance.CollisionFrequencyPositive.referenceFrequency_noncorner_positive hR hk
  intro hcorner
  apply he
  simp [cornerDepth,maxDeficit,cornerCoordinates,hcorner 0,hcorner 1,hcorner 2]

/-- The genuine extended inverse, infinite at the eight zero-frequency
points, also has finite integral.  Their nullity is proved from the
actual layer-volume bound before this AE identification. -/
theorem reference_extended_inverse_critical_finite {R:ℝ} (hR:0<R) :
    (∫⁻k in ResonantMeasure.cube R,
      (ENNReal.ofReal (referenceFrequency R k))^(-(3:ℝ)/2))<∞ := by
  have he : (∫⁻k in ResonantMeasure.cube R,
      (ENNReal.ofReal (referenceFrequency R k))^(-(3:ℝ)/2))=
      ∫⁻k in ResonantMeasure.cube R,
        ENNReal.ofReal ((referenceFrequency R k)^(-(3:ℝ)/2)) := by
    apply lintegral_congr_ae
    filter_upwards [referenceFrequency_positive_ae hR] with k hk
    exact ENNReal.ofReal_rpow_of_pos hk
  rw [he]
  exact reference_inverse_critical_lintegral hR

theorem reference_inverse_memLp_three_halves {R:ℝ} (hR:0<R) :
    MemLp (fun k=>(referenceFrequency R k)⁻¹) ((3:ℝ≥0∞)/2)
      (volume.restrict (ResonantMeasure.cube R)) := by
  have hm : AEMeasurable (referenceFrequency R)
      (volume.restrict (ResonantMeasure.cube R)) :=
    (referenceFrequency_continuousOn hR.le).aemeasurable (cube_isCompact R).measurableSet
  apply (integrable_norm_rpow_iff hm.inv.aestronglyMeasurable (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  have h := reference_inverse_critical_integrable hR
  apply h.congr
  filter_upwards [referenceFrequency_positive_ae hR] with k hk
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk)]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
  rw [←Real.rpow_neg_eq_inv_rpow]

theorem reference_inverse_integrable {R:ℝ} (hR:0<R) :
    IntegrableOn (fun k=>(referenceFrequency R k)⁻¹) (ResonantMeasure.cube R) := by
  letI : IsFiniteMeasure ((volume:Measure E).restrict (ResonantMeasure.cube R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (cube_isCompact R).measure_lt_top⟩
  apply MemLp.integrable _ (reference_inverse_memLp_three_halves hR)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
  norm_num

end
end Resonance.CornerInverseFrequency
