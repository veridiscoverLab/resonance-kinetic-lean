import Resonance.OppositeCornerBox

/-! The original conditional measure retains momentum at every output;
this converts opposite-leg events to the same two adjacent increments. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.FiberMomentumSupport
noncomputable section
open ResonantMeasure CollisionFiber OppositeCornerBox

theorem original_fiber_momentum (R : ℝ) (k : E) :
    ∀ᵐ q ∂fiberMeasure R k, q 0+q 1=q 2+q 3 := by
  unfold fiberMeasure
  apply Measure.ae_smul_measure
  have hs : MeasurableSet {q : FourMomenta | q 0+q 1=q 2+q 3} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  apply (ae_map_iff (fiberFour_measurable k).aemeasurable hs).2
  exact ae_of_all _ (fun b => fiberFour_momentum k b)

theorem original_opposite_increment (R : ℝ) (k : E) (i : Fin 3) :
    ∀ᵐ q ∂fiberMeasure R k, (q 1-k) i=(q 2-q 0) i+(q 3-q 0) i := by
  filter_upwards [original_fiber_momentum R k,fiber_support R k] with q hm hs
  have h := congrArg (fun x : E => x i) hm
  change q 0 i+q 1 i=q 2 i+q 3 i at h
  change q 1 i-k i=(q 2 i-q 0 i)+(q 3 i-q 0 i)
  have ho := congrArg (fun x : E => x i) hs.2
  linarith

end
end Resonance.FiberMomentumSupport
