import Resonance.PinnedUniformCancellation

/-! Uniform C² energy and absolute single-difference bounds for the original
Euclidean regular coarea on the circle, including all four continuous weights.
No individual collision leg is integrated before forming the difference. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff ComplexConjugate
namespace Resonance.PinnedWeakIntegrability
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedMeasureNormalization Resonance.PinnedMaximalDifference
open Resonance.PinnedCriticalCancellation Resonance.PinnedFiniteEnergy
open Resonance.PinnedSmoothDomain Resonance.PinnedUniformCancellation
open Resonance.PinnedLegACCircle
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem difference_norm_integrable_circle {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ) (hφ2 : ContDiff ℝ 2 (periodicLift φ)) :
    Integrable (fun k=>‖difference φ k‖) (circleRegularCoarea d) := by
  apply (integrable_map_measure (difference_continuous hφ).norm.aestronglyMeasurable
    quotientCoordinates_continuous.measurable.aemeasurable).mpr
  have he : (fun k=>‖difference φ k‖) ∘ quotientCoordinates=
      fun k=>‖fullDifference (periodicLift φ) k‖ :=
    funext (fun k=>congrArg norm (difference_quotient φ k))
  rw [he]
  obtain ⟨K,hK,hsub⟩ := fundamentalCell_compact_container
  exact (full_difference_integrableOn hd0 hdU hφ2 (periodicLift_periodic φ) hK).mono_set hsub

theorem difference_norm_integrable_euclideanCircle {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ) (hφ2 : ContDiff ℝ 2 (periodicLift φ)) :
    Integrable (fun k=>‖difference φ k‖) (euclideanCircleRegularCoarea d) := by
  rw [euclideanCircleRegularCoarea_eq_smul]
  exact (difference_norm_integrable_circle hd0 hdU hφ hφ2).smul_measure ENNReal.coe_ne_top

theorem difference_norm_integrable_weighted {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ) (hφ2 : ContDiff ℝ 2 (periodicLift φ)) :
    Integrable (fun k=>‖difference φ k‖) (weightedCoarea d a) := by
  obtain ⟨C,hC,hbound⟩ := weightedCoarea_le_smul d ha
  exact ((difference_norm_integrable_euclideanCircle hd0 hdU hφ hφ2).smul_measure hC).mono_measure hbound

theorem circle_c2_coarea_bounds {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    ∃ C : ℝ, 0≤C ∧ ∀ (φ : PinnedPeriodicity.Circle→ℂ), Continuous φ →
      ContDiff ℝ 2 (periodicLift φ) →
      (∫k,‖difference φ k‖ ∂circleRegularCoarea d)≤C*c2Norm (periodicLift φ) ∧
      (∫k,‖difference φ k‖^2 ∂circleRegularCoarea d)≤4*C*(c2Norm (periodicLift φ))^2 := by
  obtain ⟨K,hK,hsub⟩ := fundamentalCell_compact_container
  obtain ⟨C,hC,hall⟩ := compact_c2_coarea_estimates hd0 hdU hK
  refine ⟨C,hC,?_⟩
  intro φ hφ hφ2
  have hP := periodicLift_periodic φ
  obtain ⟨hlinear,hsquare⟩ := hall (periodicLift φ) hφ2 hP
  have hmeasure : (liftedRegularCoarea d).restrict fundamentalCell≤
      (liftedRegularCoarea d).restrict K := Measure.restrict_mono_set _ hsub
  have hi := full_difference_integrableOn hd0 hdU hφ2 hP hK
  have hi2 := full_difference_square_integrableOn hd0 hdU hφ2 hP hK
  constructor
  · unfold circleRegularCoarea
    rw [integral_map quotientCoordinates_continuous.measurable.aemeasurable
      (difference_continuous hφ).norm.aestronglyMeasurable]
    simp only [difference_quotient]
    exact (integral_mono_measure hmeasure (Eventually.of_forall (fun k=>norm_nonneg _)) hi).trans hlinear
  · unfold circleRegularCoarea
    rw [integral_map quotientCoordinates_continuous.measurable.aemeasurable
      ((difference_continuous hφ).norm.pow 2).aestronglyMeasurable]
    simp only [difference_quotient]
    exact (integral_mono_measure hmeasure (Eventually.of_forall (fun k=>sq_nonneg _)) hi2).trans hsquare

/-- Both bounds of `pin:finite-energy`, with the precise Euclidean area
normalization and an arbitrary continuous four-leg weight. -/
theorem weighted_c2_coarea_bounds {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) :
    ∃ C : ℝ, 0≤C ∧ ∀ (φ : PinnedPeriodicity.Circle→ℂ), Continuous φ →
      ContDiff ℝ 2 (periodicLift φ) →
      (∫k,‖difference φ k‖ ∂weightedCoarea d a)≤C*c2Norm (periodicLift φ) ∧
      (∫k,‖difference φ k‖^2 ∂weightedCoarea d a)≤4*C*(c2Norm (periodicLift φ))^2 := by
  obtain ⟨C,hC,hall⟩ := circle_c2_coarea_bounds hd0 hdU
  obtain ⟨W,hW,hweight⟩ := weightedCoarea_le_smul d ha
  let A : ℝ := W.toReal*(areaFactor:ℝ)
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro φ hφ hφ2
  obtain ⟨hlinear,hsquare⟩ := hall φ hφ hφ2
  have hi := difference_norm_integrable_euclideanCircle hd0 hdU hφ hφ2
  have hi2 : Integrable (fun k=>‖difference φ k‖^2) (euclideanCircleRegularCoarea d) :=
    (memLp_two_iff_integrable_sq_norm (difference_continuous hφ).aestronglyMeasurable).mp
      (difference_memLp_euclideanCircle hd0 hdU hφ hφ2)
  constructor
  · calc
      _ ≤ ∫k,‖difference φ k‖ ∂(W • euclideanCircleRegularCoarea d) :=
        integral_mono_measure hweight (Eventually.of_forall (fun k=>norm_nonneg _)) (hi.smul_measure hW)
      _ = A*(∫k,‖difference φ k‖ ∂circleRegularCoarea d) := by
        rw [euclideanCircleRegularCoarea_eq_smul,integral_smul_measure,integral_smul_measure]
        simp only [smul_eq_mul,ENNReal.coe_toReal,A]
        ring
      _ ≤ A*(C*c2Norm (periodicLift φ)) := mul_le_mul_of_nonneg_left hlinear hA
      _ = _ := by ring
  · calc
      _ ≤ ∫k,‖difference φ k‖^2 ∂(W • euclideanCircleRegularCoarea d) :=
        integral_mono_measure hweight (Eventually.of_forall (fun k=>sq_nonneg _)) (hi2.smul_measure hW)
      _ = A*(∫k,‖difference φ k‖^2 ∂circleRegularCoarea d) := by
        rw [euclideanCircleRegularCoarea_eq_smul,integral_smul_measure,integral_smul_measure]
        simp only [smul_eq_mul,ENNReal.coe_toReal,A]
        ring
      _ ≤ A*(4*C*(c2Norm (periodicLift φ))^2) := mul_le_mul_of_nonneg_left hsquare hA
      _ = _ := by ring

/-- Each tested single output is integrable only after the complete
difference has been formed. No collision-frequency integrability is assumed. -/
theorem tested_single_difference_integrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ) (hφ2 : ContDiff ℝ 2 (periodicLift φ))
    (hψ : Continuous ψ) (i : Fin 4) :
    Integrable (fun k=>difference φ k*starRingEnd ℂ (ψ (circleLeg i k))) (weightedCoarea d a) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hψ.continuousOn
  have hi := (difference_norm_integrable_weighted hd0 hdU ha hφ hφ2).const_mul B
  apply hi.mono'
    ((difference_continuous hφ).mul ((Complex.continuous_conj.comp hψ).comp
      (circleLeg_continuous i))).aestronglyMeasurable
  filter_upwards [] with k
  change ‖difference φ k*starRingEnd ℂ (ψ (circleLeg i k))‖≤B*‖difference φ k‖
  rw [norm_mul,Complex.norm_conj]
  have h := hB (circleLeg i k) (mem_univ _)
  nlinarith [norm_nonneg (difference φ k)]

end
end Resonance.PinnedWeakIntegrability
