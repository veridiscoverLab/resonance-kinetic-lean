import Resonance.MarkedFiberIsometry
import Resonance.MarkedRelativeMass

/-! Coordinate changes act simultaneously on the actual output and
the entire marked quartet, giving the same estimate on every axis. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedCoordinateSymmetry
noncomputable section
open PlaneCoarea CubeAxisCoordinates CubeAxisScaling CubeFrequencyReflection
open MarkedPhysicalConvolution MarkedPhysicalScaling MarkedFiberIsometry MarkedRelativeMass
set_option maxHeartbeats 1200000

def axisSwap (i : Fin 3) : E≃ₗᵢ[ℝ]E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 i)

theorem axisSwap_apply (i j : Fin 3) (x : E) : axisSwap i x j=x (Equiv.swap 0 i j) := by
  simp [axisSwap,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

theorem axisSwap_cube (R : ℝ) (i : Fin 3) (x : E) :
    axisSwap i x∈ResonantMeasure.cube R↔x∈ResonantMeasure.cube R := by
  change (∀j,|axisSwap i x j|≤R)↔(∀j,|x j|≤R)
  simp_rw [axisSwap_apply]
  constructor
  · intro h j
    simpa only [Equiv.swap_apply_self] using h (Equiv.swap 0 i j)
  · intro h j
    exact h _

def swapDeficits (i : Fin 3) (d : Fin 3→ℝ) (j : Fin 3) : ℝ := d (Equiv.swap 0 i j)

theorem axisSwap_output (i : Fin 3) (d : Fin 3→ℝ) (L : ℝ) :
    axisSwap i (L•normalizedOutput d)=L•normalizedOutput (swapDeficits i d) := by
  ext j
  rw [axisSwap_apply]
  rfl

def coordinateMark (L : ℝ) (i : Fin 3) (w : ℝ×ℝ→ℝ) (q : FourMomenta) : ℝ :=
  w (((q 2-q 0) i)/L,((q 3-q 0) i)/L)

theorem coordinateMark_continuous (L : ℝ) (i : Fin 3) {w : ℝ×ℝ→ℝ} (hw : Continuous w) :
    Continuous (coordinateMark L i w) := by unfold coordinateMark; fun_prop

theorem actual_axis_pullback (L : ℝ) (i : Fin 3) (w : ℝ×ℝ→ℝ) :
    pullback (axisSwap i) (scaledMark L w)=coordinateMark L i w := by
  ext q
  simp [pullback,scaledMark,axisMark,coordinateMark,axisSwap_apply,div_eq_mul_inv,mul_comm,mul_sub]

theorem all_axis_far_strip_mass {L : ℝ} (hL : 0<L) (i : Fin 3) {d : Fin 3→ℝ} {e l a b : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀j,0≤d j) (hde : ∀j,d j≤e)
    (hmax : ∃j,d j=e) (hl : 0<l) (hab : a≤b) (hfar : ∀x∈Icc a b,l≤|x|)
    {w : ℝ×ℝ→ℝ} (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1)
    (hs : ∀p,p.1∉Icc a b→w p=0) :
    FiberContinuity.fiberReadout (L/2) (coordinateMark L i w) (L•normalizedOutput d)≤
      relativeConstant*((b-a)/l)*CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) := by
  have hd1 : ∀j,d j≤1 := fun j=>(hde j).trans (by linarith)
  have hk := (cube_smul_iff hL _).mpr (normalizedOutput_mem hd0 hd1)
  have hm := original_marked_fiber_isometry (by positivity : 0≤L/2) (axisSwap i)
    (axisSwap_cube (L/2) i) (scaledMark_continuous L hw) (fun q=>hp _)
    (L•normalizedOutput d) hk
  rw [actual_axis_pullback,axisSwap_output] at hm
  have hn := geometricFrequency_isometry (by positivity : 0≤L/2) (axisSwap i)
    (axisSwap_cube (L/2) i) (L•normalizedOutput d) hk
  rw [axisSwap_output] at hn
  have hn' := congrArg ENNReal.toReal hn
  simp only [ENNReal.toReal_ofReal (CollisionFrequency.geometricFrequency_nonnegative _ _)] at hn'
  rw [←hm,←hn']
  apply actual_far_strip_mass hL he he1 (fun j=>hd0 _) (fun j=>hde _) _ hl hab hfar hw hp hb hs
  obtain ⟨j,hj⟩ := hmax
  refine ⟨Equiv.swap 0 i j,?_⟩
  simpa only [swapDeficits,Equiv.swap_apply_self] using hj

end
end Resonance.MarkedCoordinateSymmetry
