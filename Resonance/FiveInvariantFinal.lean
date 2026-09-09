import Resonance.FiveInvariantClassification
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The complete original closed cube, with its boundary null set proved,
and the five physical coordinate moments written explicitly. -/
open Set MeasureTheory Filter
open scoped Topology

namespace Resonance.FiveInvariantFinal
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants ParallelGradientAlgebra
open QuadraticCollisionInvariants QuadraticPointwiseClosure CollisionLocalization
open FiveInvariantClassification CollisionCoefficientUniqueness

theorem coordinate_quasiMeasurePreserving (j : Fin 3) :
    Measure.QuasiMeasurePreserving (fun x : E => x j) volume volume := by
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin 3 => (volume : Measure ℝ)) j).comp
    (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving

theorem cube_ae_openCube (R : ℝ) : ∀ᵐ x ∂(volume : Measure E).restrict (cube R), x∈openCube R := by
  have hn (j : Fin 3) : ∀ᵐ x ∂(volume : Measure E), x j≠R ∧ x j≠-R := by
    apply (coordinate_quasiMeasurePreserving j).ae (p := fun x : ℝ => x≠R ∧ x≠-R)
    simp only [ae_iff]
    have he : {x : ℝ | ¬(x≠R ∧ x≠-R)} = {R,-R} := by
      ext x
      simp only [mem_setOf_eq,mem_insert_iff,mem_singleton_iff]
      tauto
    rw [he]
    exact (Set.toFinite {R,-R}).measure_zero volume
  have hall := ae_all_iff.mpr hn
  rw [ae_restrict_iff' (measurable_cube R)]
  filter_upwards [hall] with x hx hxc j
  have hb := hxc j
  have hne := hx j
  by_cases hp : 0 ≤ x j
  · rw [abs_of_nonneg hp] at hb ⊢
    exact lt_of_le_of_ne hb hne.1
  · rw [abs_of_neg (lt_of_not_ge hp)] at hb ⊢
    apply lt_of_le_of_ne hb
    intro he
    apply hne.2
    linarith

theorem cube_restrict_eq_openCube (R : ℝ) :
    (volume : Measure E).restrict (cube R) = volume.restrict (openCube R) := by
  calc
    volume.restrict (cube R) = (volume.restrict (cube R)).restrict (openCube R) :=
      (Measure.restrict_eq_self_of_ae_mem (cube_ae_openCube R)).symm
    _ = volume.restrict (openCube R) := by
      rw [Measure.restrict_restrict (openCube_isOpen R).measurableSet,
        inter_eq_left.mpr (openCube_subset_cube R)]

theorem linear_coordinates (b : E →L[ℝ] ℝ) (x : E) :
    b x = ∑ j : Fin 3, b (axisPoint 1 j)*x j := by
  conv_lhs => rw [vector_axis_expansion x]
  simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

theorem evaluate_five_moments (b : Coefficients) (x : E) :
    evaluate b x = b.1+(∑ j : Fin 3, b.2.1 (axisPoint 1 j)*x j)+b.2.2*‖x‖^2 := by
  unfold evaluate
  rw [linear_coordinates]

theorem original_cube_invariant_unique {R : ℝ} (hR : 0<R) {f : E → ℝ}
    (hfl : LocallyIntegrableOn f (openCube R)) (hf : invariant R f) :
    ∃! b : Coefficients,
      f =ᵐ[(volume : Measure E).restrict (cube R)] evaluate b := by
  rw [cube_restrict_eq_openCube]
  exact locally_integrable_collision_invariant_unique hR hfl hf

theorem original_cube_five_moments {R : ℝ} (hR : 0<R) {f : E → ℝ}
    (hfl : LocallyIntegrableOn f (openCube R)) (hf : invariant R f) :
    ∃ a c : ℝ, ∃ b : Fin 3 → ℝ, ∀ᵐ x ∂(volume : Measure E).restrict (cube R),
      f x=a+(∑ j : Fin 3,b j*x j)+c*‖x‖^2 := by
  obtain ⟨b,hb,_hu⟩ := original_cube_invariant_unique hR hfl hf
  exact ⟨b.1,b.2.2,fun j => b.2.1 (axisPoint 1 j),hb.mono
    (fun x hx => hx.trans (evaluate_five_moments b x))⟩

end
end Resonance.FiveInvariantFinal
