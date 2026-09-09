import Resonance.PinnedCriticalCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Exact volume normalization of the original periodic critical gauges and
the two actual nonlinear critical coordinate replacements. -/
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace Resonance.PinnedCriticalVolume
noncomputable section
open PinnedMeasure PinnedCriticalFactor PinnedCriticalNormalization PinnedLegAC
open CoordinateReplacement PinnedCriticalCoordinates

theorem rectangleMap_det : rectangleMap.toLinearMap.det=1 := by
  rw [←LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3))]
  simp only [Matrix.det_fin_three, LinearMap.toMatrix_apply, PiLp.basisFun_repr,
    PiLp.basisFun_apply]
  norm_num [rectangleMap, show (2:Fin 3)≠1 by decide, show (0:Fin 3)≠2 by decide,
    show (1:Fin 3)≠2 by decide, show (2:Fin 3)≠0 by decide, Matrix.cons_val_succ]
  change -(0:ℝ)-0+1=1
  norm_num

theorem exchangeIncoming_det : exchangeIncoming.toLinearMap.det = -1 := by
  rw [←LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3))]
  simp only [Matrix.det_fin_three, LinearMap.toMatrix_apply, PiLp.basisFun_repr,
    PiLp.basisFun_apply]
  norm_num [exchangeIncoming, show (2:Fin 3)≠1 by decide, show (0:Fin 3)≠2 by decide,
    show (1:Fin 3)≠2 by decide, show (2:Fin 3)≠0 by decide, Matrix.cons_val_succ]
  rfl

theorem rectangleMap_volume_preserving : MeasurePreserving rectangleMap volume volume := by
  refine ⟨rectangleMap.continuous.measurable, ?_⟩
  change Measure.map rectangleMap.toLinearMap volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [rectangleMap_det]; norm_num)]
  simp [rectangleMap_det]

theorem exchangeIncoming_volume_preserving : MeasurePreserving exchangeIncoming volume volume := by
  refine ⟨exchangeIncoming.continuous.measurable, ?_⟩
  change Measure.map exchangeIncoming.toLinearMap volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [exchangeIncoming_det]; norm_num)]
  simp [exchangeIncoming_det]

theorem criticalGauge_volume_preserving (swap : Bool) (n m : ℤ) :
    MeasurePreserving (criticalGauge swap n m) volume volume := by
  have htrans := (measurePreserving_add_right (volume : Measure Ambient)
    (PinnedPeriodicity.latticeShift ![n,m,0])).comp rectangleMap_volume_preserving
  cases swap
  · exact htrans
  · exact exchangeIncoming_volume_preserving.comp htrans

theorem qCoordinates_exact_volume {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {S : Set Ambient} (hS : MeasurableSet S) (hi : InjOn (qCoordinates d) S)
    (B : Ambient → ℝ≥0∞) :
    (∫⁻q in qCoordinates d '' S, B q) = ∫⁻p in S,
      ENNReal.ofReal |(fderiv ℝ (sharedFactor d) p) (CoordinateReplacement.unit 0)| *
        B (qCoordinates d p) :=
  exact_volume_change 0 hS (fun p _ =>
    (sharedFactor_contDiff_one hd0 hdU).differentiable (by norm_num) p) hi B

theorem vCoordinates_exact_volume {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {S : Set Ambient} (hS : MeasurableSet S) (hi : InjOn (vCoordinates d) S)
    (B : Ambient → ℝ≥0∞) :
    (∫⁻q in vCoordinates d '' S, B q) = ∫⁻p in S,
      ENNReal.ofReal |sharedFactor d p + p 2 *
        (fderiv ℝ (sharedFactor d) p) (CoordinateReplacement.unit 2)| * B (vCoordinates d p) := by
  have hd : ∀p : Ambient, DifferentiableAt ℝ (fun q : Ambient => q 2*sharedFactor d q) p :=
    fun p => (coordinateProjection 2).differentiableAt.mul
      ((sharedFactor_contDiff_one hd0 hdU).differentiable (by norm_num) p)
  have h := exact_volume_change 2 hS (fun p _ => hd p) hi B
  change (∫⁻q in vCoordinates d '' S, B q) = _ at h
  rw [h]
  apply lintegral_congr
  intro p
  have hder := (coordinateProjection 2).hasFDerivAt.mul
    ((sharedFactor_contDiff_one hd0 hdU).differentiable (by norm_num) p).hasFDerivAt
  change HasFDerivAt (fun q : Ambient => q 2*sharedFactor d q)
    (p 2 • fderiv ℝ (sharedFactor d) p + sharedFactor d p • coordinateProjection 2) p at hder
  rw [hder.fderiv]
  simp [coordinateProjection, CoordinateReplacement.unit, add_comm, vCoordinates]

end
end Resonance.PinnedCriticalVolume
