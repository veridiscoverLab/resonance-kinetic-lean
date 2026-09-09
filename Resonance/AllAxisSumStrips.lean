import Resonance.SumStripMass
import Resonance.MarkedCoordinateSymmetry

/-! Far sum strips on every coordinate of the original fixed-output
quartet, with the original full collision frequency. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.AllAxisSumStrips
noncomputable section
open PlaneCoarea CubeAxisCoordinates CubeAxisScaling CubeFrequencyReflection
open MarkedPhysicalConvolution MarkedPhysicalScaling MarkedFiberIsometry MarkedRelativeMass
open MarkedCoordinateSymmetry SumStripMass
set_option maxHeartbeats 1200000

theorem original_all_axis_sum_strip {L : ℝ} (hL : 0 < L) (i : Fin 3)
    {d : Fin 3 → ℝ} {e l a b : ℝ}
    (he : 0 < e) (he1 : e ≤ (1:ℝ)/4096) (hd0 : ∀j,0 ≤ d j) (hde : ∀j,d j ≤ e)
    (hmax : ∃j,d j=e) (hl : 0 < l) (hab : a ≤ b) (hfar : ∀s∈Icc a b,l ≤ |s|)
    {w : ℝ×ℝ → ℝ} (hw : Continuous w) (hp : ∀p,0 ≤ w p) (hb : ∀p,w p ≤ 1)
    (hs : ∀p,p.1+p.2∉Icc a b → w p=0) :
    FiberContinuity.fiberReadout (L/2) (coordinateMark L i w) (L•normalizedOutput d) ≤
      relativeConstant*((4/l)*(b-a+8*e/l))*
        CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) := by
  have hd1 : ∀j,d j ≤ 1 := fun j => (hde j).trans (by linarith)
  have hk := (cube_smul_iff hL _).mpr (normalizedOutput_mem hd0 hd1)
  have hm := original_marked_fiber_isometry (by positivity : 0 ≤ L/2) (axisSwap i)
    (axisSwap_cube (L/2) i) (scaledMark_continuous L hw) (fun q => hp _)
    (L•normalizedOutput d) hk
  rw [actual_axis_pullback,axisSwap_output] at hm
  have hn := geometricFrequency_isometry (by positivity : 0 ≤ L/2) (axisSwap i)
    (axisSwap_cube (L/2) i) (L•normalizedOutput d) hk
  rw [axisSwap_output] at hn
  have hn' := congrArg ENNReal.toReal hn
  simp only [ENNReal.toReal_ofReal (CollisionFrequency.geometricFrequency_nonnegative _ _)] at hn'
  rw [←hm,←hn']
  apply original_far_sum_strip_mass hL he he1 (fun j => hd0 _) (fun j => hde _)
    _ hl hab hfar hw hp hb hs
  obtain ⟨j,hj⟩ := hmax
  refine ⟨Equiv.swap 0 i j,?_⟩
  simpa only [swapDeficits,Equiv.swap_apply_self] using hj

end
end Resonance.AllAxisSumStrips
