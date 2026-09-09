import Resonance.PinnedFiniteEnergy
import Resonance.PinnedMaximalDifference
import Resonance.SmoothCircleDensity

/-! Actual periodic C² functions lie in the maximal full-difference domain.
All integrals retain the complete signed four-leg difference. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace Resonance.PinnedSmoothDomain
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedMeasureNormalization Resonance.PinnedClassificationFinal
open Resonance.PinnedLegACCircle Resonance.PinnedMaximalDifference
open Resonance.PinnedCriticalCancellation Resonance.PinnedFiniteEnergy
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

theorem fundamentalCell_compact_container :
    ∃ K : Set Ambient, IsCompact K ∧ fundamentalCell ⊆ K := by
  let B : Set (Fin 3→ℝ) := Icc (fun _=>0) (fun _=>period)
  let K : Set Ambient := (WithLp.toLp 2) '' B
  refine ⟨K,isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin 3=>ℝ)),?_⟩
  intro k hk
  refine ⟨WithLp.ofLp k,?_,by simp⟩
  exact ⟨fun i=>(hk i).1,fun i=>(hk i).2.le⟩

theorem full_difference_memLp_cell {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period) :
    MemLp (fullDifference φ) 2 (cellCoarea d) := by
  obtain ⟨K,hK,hsub⟩ := fundamentalCell_compact_container
  apply (memLp_two_iff_integrable_sq_norm
    (fullDifference_continuous hφ.continuous).aestronglyMeasurable).mpr
  exact (full_difference_square_integrableOn hd0 hdU hφ hp hK).mono_set hsub

theorem difference_continuous {φ : PinnedPeriodicity.Circle→ℂ}
    (hφ : Continuous φ) : Continuous (difference φ) :=
  (((hφ.comp (circleLeg_continuous 0)).add (hφ.comp (circleLeg_continuous 1))).sub
    (hφ.comp (circleLeg_continuous 2))).sub (hφ.comp (circleLeg_continuous 3))

theorem difference_quotient (φ : PinnedPeriodicity.Circle→ℂ) (k : Ambient) :
    difference φ (quotientCoordinates k)=fullDifference (periodicLift φ) k := by
  simp [difference,circleLeg,quotientCoordinates,fullDifference,periodicLift]

theorem difference_memLp_circle {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) :
    MemLp (difference φ) 2 (circleRegularCoarea d) := by
  apply (memLp_map_measure_iff (difference_continuous hφ).aestronglyMeasurable
    quotientCoordinates_continuous.measurable.aemeasurable).mpr
  have he : difference φ ∘ quotientCoordinates=fullDifference (periodicLift φ) :=
    funext (difference_quotient φ)
  rw [he]
  exact full_difference_memLp_cell hd0 hdU hφ2 (periodicLift_periodic φ)

theorem difference_memLp_euclideanCircle {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) :
    MemLp (difference φ) 2 (euclideanCircleRegularCoarea d) := by
  rw [euclideanCircleRegularCoarea_eq_smul]
  exact (difference_memLp_circle hd0 hdU hφ hφ2).smul_measure ENNReal.coe_ne_top

theorem weightedCoarea_le_smul (d : ℝ) {a : FourCircle→ℝ} (ha : Continuous a) :
    ∃ C : ℝ≥0∞, C≠(∞:ℝ≥0∞) ∧ weightedCoarea d a≤C • euclideanCircleRegularCoarea d := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  refine ⟨ENNReal.ofReal B,ENNReal.ofReal_ne_top,?_⟩
  unfold weightedCoarea
  rw [← withDensity_const]
  apply withDensity_mono
  exact Eventually.of_forall (fun k => ENNReal.ofReal_le_ofReal
    (le_trans (le_abs_self _) (hB (fullLegs k) (mem_univ _))))

theorem difference_memLp_weighted {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) :
    MemLp (difference φ) 2 (weightedCoarea d a) := by
  obtain ⟨C,hC,hbound⟩ := weightedCoarea_le_smul d ha
  exact ((difference_memLp_euclideanCircle hd0 hdU hφ hφ2).smul_measure hC).mono_measure hbound

theorem continuous_C2_mem_domain {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (φ : C(PinnedPeriodicity.Circle,ℂ))
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) :
    ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ ∈
      (maximalDifference hd0 hdU a).domain := by
  apply (maximalDifference_domain_iff hd0 hdU a _).mpr
  have he : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ :
      PinnedPeriodicity.Circle→ℂ) =ᵐ[circleHaar] φ := ContinuousMap.coeFn_toLp circleHaar φ
  exact (difference_memLp_weighted hd0 hdU ha φ.continuous hφ2).ae_eq
    (difference_ae_congr hd0 hdU a he.symm)

theorem maximalDifference_dense_domain {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) :
    Dense ((maximalDifference hd0 hdU a).domain : Set Source) := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨φ,hφ,hp,hclose⟩ :=
    Resonance.SmoothCircleDensity.exists_smooth_periodic_approximation u hε
  exact ⟨ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ,
    continuous_C2_mem_domain hd0 hdU ha φ
      (hφ.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))),
    by simpa only [dist_comm] using hclose⟩

end
end Resonance.PinnedSmoothDomain
