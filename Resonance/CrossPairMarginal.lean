import Resonance.PlaneGlobal
import Mathlib.MeasureTheory.Group.Prod

/-! Exact incoming--outgoing pair coordinates for the same complete
coarea measure.  The plane orthogonal to the relative momentum and all
four original cube flags remain internal to this representation. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CrossPairMarginal
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure
open PlaneCoarea (E2 Ray rayMeasure planePoint rectangleFour rectangleFour_continuous
  plane_joint_measurable normalCoords_zero planePoint_eq)
open PlaneGlobal (rayOne planeBase PlaneParameters planeShell direction direction_measurable
  direction_polar rayMeasure_from_rayOne)
open PolarCoordinates (polarVector polarVector_preserves_volume)

def cartesianPlane (p : PlaneParameters) : E×(E×E2) :=
  (p.1,(polarVector p.2.1,p.2.2))

def fullPlaneBase : Measure PlaneParameters :=
  (volume : Measure E).prod (rayMeasure.prod (volume : Measure E2))

theorem cartesianPlane_preserving : MeasurePreserving cartesianPlane fullPlaneBase
    ((volume : Measure E).prod ((volume : Measure E).prod (volume : Measure E2))) := by
  letI : SigmaFinite (surface.prod (Measure.volumeIoiPow 2)) := inferInstance
  letI : SigmaFinite ((surface.prod (Measure.volumeIoiPow 2)).prod (volume : Measure E2)) :=
    inferInstance
  exact (MeasurePreserving.id (volume : Measure E)).prod
    (polarVector_preserves_volume.prod (MeasurePreserving.id (volume : Measure E2)))

theorem rayOne_from_rayMeasure : rayOne=rayMeasure.withDensity
    (fun p : Ray=>ENNReal.ofReal ((p.2 : ℝ)⁻¹)) := by
  rw [rayMeasure_from_rayOne]
  have hm : Measurable (fun p : Ray=>ENNReal.ofReal (p.2 : ℝ)) := by fun_prop
  have h := withDensity_inv_same (μ := rayOne) hm
    (ae_of_all _ (fun p=>ne_of_gt (ENNReal.ofReal_pos.mpr p.2.property)))
    (ae_of_all _ (fun _=>ENNReal.ofReal_ne_top))
  have he : (fun p : Ray=>ENNReal.ofReal ((p.2 : ℝ)⁻¹))=
      fun p => (ENNReal.ofReal (p.2 : ℝ))⁻¹ := by
    funext p
    exact ENNReal.ofReal_inv_of_pos p.2.property
  rw [he]
  exact h.symm

theorem planeBase_from_fullPlaneBase : planeBase=fullPlaneBase.withDensity
    (fun p : PlaneParameters=>ENNReal.ofReal ((p.2.1.2 : ℝ)⁻¹)) := by
  rw [planeBase,rayOne_from_rayMeasure,prod_withDensity_left (by fun_prop),
    prod_withDensity_right (by fun_prop)]
  rfl

def relativeQuartet (p : E×(E×E2)) : FourMomenta :=
  rectangleFour p.1 p.2.1 (planePoint (direction p.2.1) p.2.2)

theorem relativeQuartet_measurable : Measurable relativeQuartet := by
  have hd : Measurable (fun p : E×(E×E2)=>(direction p.2.1,p.2.2)) :=
    (direction_measurable.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have hh := plane_joint_measurable.comp hd
  have hp : Measurable (fun p : E×(E×E2)=>planePoint (direction p.2.1) p.2.2) := by
    simpa only [Function.comp_def,planePoint_eq] using hh
  have hm : Measurable (fun p : E×(E×E2)=>(p.1,(p.2.1,
      planePoint (direction p.2.1) p.2.2))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hp)
  exact rectangleFour_continuous.measurable.comp hm

theorem relativeQuartet_cartesianPlane (p : PlaneParameters) :
    relativeQuartet (cartesianPlane p)=planeShell p 0 := by
  simp only [relativeQuartet,cartesianPlane,polarVector,direction_polar,planeShell,
    zero_div,normalCoords_zero,planePoint_eq]

theorem cartesianPlane_norm (p : PlaneParameters) :
    ‖(cartesianPlane p).2.1‖=(p.2.1.2 : ℝ) := by
  have hr : 0 < (p.2.1.2 : ℝ) := p.2.1.2.property
  simp [cartesianPlane,polarVector,norm_smul,abs_of_pos hr]

theorem planeBase_relative_lintegral (Φ : FourMomenta→ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ p,Φ (planeShell p 0) ∂planeBase)=
      ∫⁻ p,ENNReal.ofReal (‖p.2.1‖⁻¹)*Φ (relativeQuartet p)
        ∂((volume : Measure E).prod ((volume : Measure E).prod (volume : Measure E2))) := by
  rw [planeBase_from_fullPlaneBase]
  have hwd := lintegral_withDensity_eq_lintegral_mul fullPlaneBase
    (f := fun p : PlaneParameters=>ENNReal.ofReal ((p.2.1.2 : ℝ)⁻¹)) (by fun_prop)
    (g := fun p=>Φ (planeShell p 0)) (hΦ.comp PlaneGlobal.planeShell_zero_measurable)
  rw [hwd]
  have h := cartesianPlane_preserving.lintegral_comp
    ((show Measurable (fun p : E×(E×E2)=>ENNReal.ofReal (‖p.2.1‖⁻¹)) by fun_prop).mul
      (hΦ.comp relativeQuartet_measurable))
  simpa only [Pi.mul_apply,Function.comp_def,cartesianPlane_norm,
    relativeQuartet_cartesianPlane] using h

end
end Resonance.CrossPairMarginal
