import Resonance.ActualStripEvents
import Resonance.AllAxisSumStrips
import Resonance.FixedOutputMeasureSymmetry
import Resonance.FiberMomentumSupport

/-! Actual measurable strip events for both adjacent legs and the
opposite leg, on the same original fixed-output conditional measure. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.RoleStripEvents
noncomputable section
open ResonantMeasure CollisionFiber CollisionFrequency FiberContinuity CubeAxisCoordinates
open MarkedCoordinateSymmetry MarkedRelativeMass IntervalMajorant ActualStripEvents
open FixedOutputMeasureSymmetry AllAxisSumStrips FiberMomentumSupport
set_option maxHeartbeats 1200000

def secondAxisStrip (L : ℝ) (i : Fin 3) (a b : ℝ) : Set FourMomenta :=
  {q | ((q 3-q 0) i)/L∈Icc a b}

theorem second_axis_mass_eq {R : ℝ} (hR : 0 < R) (k : E) (hk : k∈cube R)
    (L : ℝ) (i : Fin 3) (a b : ℝ) :
    fiberMeasure R k (secondAxisStrip L i a b)=fiberMeasure R k (axisStrip L i a b) := by
  have h := congrArg (fun μ : Measure FourMomenta => μ (axisStrip L i a b))
    (original_fiber_outgoing hR k hk)
  dsimp only at h
  rw [Measure.map_apply FixedOutputOutgoing.swapOutgoingK_continuous.measurable
    (axisStrip_measurable L i a b)] at h
  exact h

def sumAxisStrip (L : ℝ) (i : Fin 3) (a b : ℝ) : Set FourMomenta :=
  {q | ((q 2-q 0) i)/L+((q 3-q 0) i)/L∈Icc a b}

def oppositeAxisStrip (L : ℝ) (i : Fin 3) (k : E) (a b : ℝ) : Set FourMomenta :=
  {q | ((q 1-k) i)/L∈Icc a b}

theorem sumAxisStrip_measurable (L : ℝ) (i : Fin 3) (a b : ℝ) :
    MeasurableSet (sumAxisStrip L i a b) := measurableSet_Icc.preimage (by fun_prop)

theorem opposite_sum_mass_eq (R L : ℝ) (k : E) (i : Fin 3) (a b : ℝ) :
    fiberMeasure R k (oppositeAxisStrip L i k a b)=fiberMeasure R k (sumAxisStrip L i a b) := by
  apply measure_congr
  filter_upwards [original_opposite_increment R k i] with q hq
  apply propext
  change ((q 1-k) i)/L∈Icc a b ↔ ((q 2-q 0) i)/L+((q 3-q 0) i)/L∈Icc a b
  rw [hq,add_div]

theorem original_opposite_strip_event {L : ℝ} (hL : 0 < L) (i : Fin 3) {d : Fin 3→ℝ}
    {e l a b ε : ℝ} (he : 0 < e) (he1 : e ≤ (1:ℝ)/4096)
    (hd0 : ∀j,0 ≤ d j) (hde : ∀j,d j ≤ e) (hmax : ∃j,d j=e)
    (hl : 0 < l) (hab : a ≤ b) (hε : 0 < ε)
    (hfar : ∀s∈Icc (a-ε) (b+ε),l ≤ |s|) :
    fiberMeasure (L/2) (L•normalizedOutput d)
      (oppositeAxisStrip L i (L•normalizedOutput d) a b) ≤
      ENNReal.ofReal (relativeConstant*((4/l)*(b-a+2*ε+8*e/l))*
        geometricFrequency (L/2) (L•normalizedOutput d)) := by
  rw [opposite_sum_mass_eq]
  let w : ℝ×ℝ→ℝ := fun p => majorant a b ε (p.1+p.2)
  have hw : Continuous w := (majorant_continuous a b ε).comp (continuous_fst.add continuous_snd)
  have hp : ∀p,0 ≤ w p := fun p => (majorant_bounds a b ε (p.1+p.2)).1
  have hb : ∀p,w p ≤ 1 := fun p => (majorant_bounds a b ε (p.1+p.2)).2
  have hs : ∀p,p.1+p.2∉Icc (a-ε) (b+ε) → w p=0 := fun _ h => majorant_support hε h
  have hmajor := actual_fiber_measure_majorant (by positivity : 0 ≤ L/2) (L•normalizedOutput d)
    (sumAxisStrip_measurable L i a b) (coordinateMark_continuous L i hw).measurable
    (fun q => hp _) (fun q => hb _) (fun q hq => by
      change 1 ≤ majorant a b ε (((q 2-q 0) i)/L+((q 3-q 0) i)/L)
      rw [majorant_one hε hq])
  have hm := original_all_axis_sum_strip hL i he he1 hd0 hde hmax hl (by linarith) hfar hw hp hb hs
  have heq : (b+ε)-(a-ε)+8*e/l=b-a+2*ε+8*e/l := by ring
  rw [heq] at hm
  exact hmajor.trans (ENNReal.ofReal_le_ofReal hm)

end
end Resonance.RoleStripEvents
