import Resonance.IntervalMajorant

/-! The original measurable adjacent-leg strip event is controlled
using an explicitly constructed continuous mark of the same quartet. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.ActualStripEvents
noncomputable section
open PlaneCoarea CollisionFiber CollisionFrequency FiberContinuity CubeAxisCoordinates
open MarkedCoordinateSymmetry MarkedRelativeMass IntervalMajorant
set_option maxHeartbeats 1000000

def axisStrip (L : ℝ) (i : Fin 3) (a b : ℝ) : Set FourMomenta :=
  {q | ((q 2-q 0) i)/L∈Icc a b}

theorem axisStrip_measurable (L : ℝ) (i : Fin 3) (a b : ℝ) : MeasurableSet (axisStrip L i a b) :=
  measurableSet_Icc.preimage (by fun_prop)

theorem original_axis_strip_event {L : ℝ} (hL : 0<L) (i : Fin 3) {d : Fin 3→ℝ}
    {e l a b ε : ℝ} (he : 0<e) (he1 : e≤(1:ℝ)/4096)
    (hd0 : ∀j,0≤d j) (hde : ∀j,d j≤e) (hmax : ∃j,d j=e)
    (hl : 0<l) (hab : a≤b) (hε : 0<ε)
    (hfar : ∀s∈Icc (a-ε) (b+ε),l≤|s|) :
    fiberMeasure (L/2) (L•normalizedOutput d) (axisStrip L i a b)≤
      ENNReal.ofReal (relativeConstant*((b-a+2*ε)/l)*
        geometricFrequency (L/2) (L•normalizedOutput d)) := by
  let w : ℝ×ℝ→ℝ := fun p=>majorant a b ε p.1
  have hw : Continuous w := (majorant_continuous a b ε).comp continuous_fst
  have hp : ∀p,0≤w p := fun p=>(majorant_bounds a b ε p.1).1
  have hb : ∀p,w p≤1 := fun p=>(majorant_bounds a b ε p.1).2
  have hs : ∀p,p.1∉Icc (a-ε) (b+ε)→w p=0 := fun _ h=>majorant_support hε h
  have hmajor := actual_fiber_measure_majorant (by positivity : 0≤L/2) (L•normalizedOutput d)
    (axisStrip_measurable L i a b) (coordinateMark_continuous L i hw).measurable
    (fun q=>hp _) (fun q=>hb _) (fun q hq=>by
      change 1 ≤ majorant a b ε (((q 2-q 0) i)/L)
      rw [majorant_one hε hq])
  have hm := all_axis_far_strip_mass hL i he he1 hd0 hde hmax hl (by linarith) hfar hw hp hb hs
  have heq : (b+ε)-(a-ε)=b-a+2*ε := by ring
  rw [heq] at hm
  exact hmajor.trans (ENNReal.ofReal_le_ofReal hm)

end
end Resonance.ActualStripEvents
