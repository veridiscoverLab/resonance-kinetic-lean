import Resonance.FiberContinuity

/-! All coordinate latitudes are null for the actual `volume.toSphere`.
The proof uses its defining radial cone and real finite fibers; no
unproved identification with a Hausdorff surface measure is used. -/
open MeasureTheory Set Real
open scoped ENNReal Pointwise
namespace Resonance.SphereLatitudeNull
noncomputable section
set_option maxHeartbeats 600000
open ResonantMeasure
open PlaneCoarea (E2 splitCoords splitCoords_symm splitCoords_preserving)

theorem quadratic_fiber_finite (a b : ℝ) (ha : a^2 ≠ 1) :
    {t : ℝ | t^2 = a^2 * (t^2+b)}.Finite := by
  by_cases h : {t : ℝ | t^2 = a^2 * (t^2+b)}.Nonempty
  · obtain ⟨t₀, ht₀⟩ := h
    apply Set.Finite.subset (Set.toFinite ({t₀,-t₀} : Set ℝ))
    intro t ht
    have he : (1-a^2)*(t^2-t₀^2) = 0 := by
      change t^2 = a^2*(t^2+b) at ht
      change t₀^2 = a^2*(t₀^2+b) at ht₀
      nlinarith
    have hsq : t^2=t₀^2 := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by
      intro h0
      apply ha
      linarith))
    simpa only [mem_insert_iff, mem_singleton_iff] using (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
  · simpa only [not_nonempty_iff_eq_empty.mp h] using (finite_empty : (∅ : Set ℝ).Finite)

def quadraticCone (a : ℝ) (j : Fin 3) : Set E := {x | x j ^ 2 = a^2 * ‖x‖^2}

theorem quadraticCone_measurable (a : ℝ) (j : Fin 3) :
    MeasurableSet (quadraticCone a j) := measurableSet_eq_fun (by fun_prop) (by fun_prop)

theorem split_norm_sq (t : ℝ) (z : E2) :
    ‖splitCoords.symm (t,z)‖^2 = t^2 + ‖z‖^2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    splitCoords_symm, PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.cons_zero, Fin.cons_succ, PlaneCoarea.real_inner_apply]
  ring

theorem quadraticCone_zero_null (a : ℝ) (ha : a^2 ≠ 1) :
    (volume : Measure E) (quadraticCone a 0) = 0 := by
  let f : E2×ℝ → E := fun p => splitCoords.symm (p.2,p.1)
  have hf : MeasurePreserving f ((volume : Measure E2).prod volume) volume :=
    splitCoords_preserving.symm.comp Measure.measurePreserving_swap
  rw [← hf.map_eq, Measure.map_apply hf.measurable (quadraticCone_measurable a 0),
    Measure.prod_apply ((quadraticCone_measurable a 0).preimage hf.measurable)]
  have hz (z : E2) : (volume : Measure ℝ) {t | f (z,t) ∈ quadraticCone a 0} = 0 := by
    have he : {t | f (z,t) ∈ quadraticCone a 0} =
        {t : ℝ | t^2 = a^2*(t^2+‖z‖^2)} := by
      ext t
      simp only [f, quadraticCone, mem_setOf_eq, split_norm_sq]
      rw [splitCoords_symm]
      rfl
    rw [he]
    exact (quadratic_fiber_finite a (‖z‖^2) ha).measure_zero volume
  change (∫⁻ z : E2, (volume : Measure ℝ) {t | f (z,t) ∈ quadraticCone a 0}) = 0
  simp_rw [hz]
  exact lintegral_zero

theorem quadraticCone_null (a : ℝ) (ha : a^2 ≠ 1) (j : Fin 3) :
    (volume : Measure E) (quadraticCone a j) = 0 := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 j)
  have he (x : E) : e x 0 = x j := by
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have hp : e ⁻¹' quadraticCone a 0 = quadraticCone a j := by
    ext x
    simp only [mem_preimage, quadraticCone, mem_setOf_eq, he, e.norm_map]
  rw [← hp, e.measurePreserving.measure_preimage (quadraticCone_measurable a 0).nullMeasurableSet]
  exact quadraticCone_zero_null a ha

theorem sphere_coordinate_level_null (j : Fin 3) (a : ℝ) :
    surface {σ : Sphere | (σ:E) j = a} = 0 := by
  by_cases ha : a^2 = 1
  · apply measure_mono_null (t := {σ : Sphere | (σ:E) j^2=1})
    · intro σ hσ
      change (σ:E) j = a at hσ
      change (σ:E) j^2=1
      rw [hσ, ha]
    · exact FiberContinuity.sphere_coordinate_extreme_null j
  · have hs : MeasurableSet {σ : Sphere | (σ:E) j = a} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    rw [surface, Measure.toSphere_apply' _ hs]
    have hsub : Ioo (0:ℝ) 1 • ((↑) '' {σ : Sphere | (σ:E) j=a}) ⊆
        quadraticCone a j := by
      rintro x ⟨r,hr,y,⟨σ,hσ,rfl⟩,rfl⟩
      change (σ:E) j = a at hσ
      change (r * (σ:E) j)^2 = a^2 * ‖r • (σ:E)‖^2
      rw [hσ, norm_smul, sphere_norm, mul_one, Real.norm_eq_abs, sq_abs]
      ring
    rw [measure_mono_null hsub (quadraticCone_null a ha j), mul_zero]

end
end Resonance.SphereLatitudeNull
