import Resonance.FreeTransport
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The physical spatial torus of period 2π is mapped to the unit-coordinate
torus by the actual scaling X↦X/(2π). Probability Haar measure is preserved;
this is a coordinate dictionary, not a change of physical frequency or time. -/
open Set MeasureTheory
namespace Resonance.SpatialTorusNormalization
noncomputable section
open FreeTransport
abbrev UnitTorus := UnitAddTorus (Fin 3)

def coordinateCircle : AddCircle period≃ₜ+UnitAddCircle where
  toAddEquiv := AddCircle.equivAddCircle period 1 (ne_of_gt periodPositive.out) one_ne_zero
  continuous_toFun := (AddCircle.homeomorphAddCircle period 1 (ne_of_gt periodPositive.out) one_ne_zero).continuous
  continuous_invFun := (AddCircle.homeomorphAddCircle period 1 (ne_of_gt periodPositive.out) one_ne_zero).symm.continuous

def coordinates : SpatialTorus≃ₜ+UnitTorus where
  toFun x:=fun j=>coordinateCircle (x j)
  invFun y:=fun j=>coordinateCircle.symm (y j)
  left_inv x:=by funext j; exact coordinateCircle.left_inv (x j)
  right_inv y:=by funext j; exact coordinateCircle.right_inv (y j)
  map_add' x y:=by funext j; exact coordinateCircle.map_add _ _
  continuous_toFun:=continuous_pi (fun j=>coordinateCircle.continuous.comp (continuous_apply j))
  continuous_invFun:=continuous_pi (fun j=>coordinateCircle.symm.continuous.comp (continuous_apply j))

def spatialHaar : Measure SpatialTorus := Measure.pi (fun _:Fin 3=>AddCircle.haarAddCircle (T:=period))

instance spatialHaar_probability : IsProbabilityMeasure spatialHaar := by
  unfold spatialHaar
  infer_instance

instance spatialHaar_addHaar : Measure.IsAddHaarMeasure spatialHaar := by
  unfold spatialHaar
  infer_instance

def unitHaar : Measure UnitTorus := Measure.pi (fun _:Fin 3=>AddCircle.haarAddCircle (T:=1))
instance unitHaar_probability : IsProbabilityMeasure unitHaar := by
  unfold unitHaar
  infer_instance
instance unitHaar_addHaar : Measure.IsAddHaarMeasure unitHaar := by
  unfold unitHaar
  infer_instance

theorem coordinates_preserving : MeasurePreserving coordinates spatialHaar unitHaar :=
  AddMonoidHom.measurePreserving (f:=coordinates.toAddMonoidHom) coordinates.continuous
    coordinates.surjective (by simp)

theorem coordinates_inverse_preserving : MeasurePreserving coordinates.symm
    unitHaar spatialHaar :=
  AddMonoidHom.measurePreserving (f:=coordinates.symm.toAddMonoidHom) coordinates.symm.continuous
    coordinates.symm.surjective (by simp)

theorem coordinates_real (X : Fin 3→ℝ) (j : Fin 3) :
    coordinates (fun i=>(X i : AddCircle period)) j=
      (X j/period : ℝ) := by
  change AddCircle.equivAddCircle period 1 (ne_of_gt periodPositive.out) one_ne_zero
    (X j : AddCircle period)=((X j/period : ℝ):UnitAddCircle)
  rw [AddCircle.equivAddCircle_apply_mk]
  simp only [mul_one,div_eq_mul_inv]

end
end Resonance.SpatialTorusNormalization
