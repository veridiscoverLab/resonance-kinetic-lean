import Resonance.JetMildEquation
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! The physical phase measure and its exact transport invariance. The momentum
measure is the restriction of the original Euclidean volume to the entire
closed cube, including its boundary; the space measure is Haar volume on the
original torus of period 2π. -/
open Set MeasureTheory
namespace Resonance.PhaseEnergy
noncomputable section
open FreeTransport ResonantMeasure

attribute [local instance] Measure.Subtype.measureSpace

def momentumMeasure (R : ℝ) : Measure (MomentumDomain R) := volume

theorem momentumMeasure_mass (R : ℝ) :
    momentumMeasure R univ = volume (cube R) :=
  Measure.Subtype.volume_univ (cube_isCompact R).measurableSet.nullMeasurableSet

instance momentumMeasure_finite (R : ℝ) : IsFiniteMeasure (momentumMeasure R) :=
  ⟨by rw [momentumMeasure_mass]; exact (cube_isCompact R).measure_lt_top⟩

theorem momentumMeasure_map (R : ℝ) :
    (momentumMeasure R).map ((↑) : MomentumDomain R → E) = volume.restrict (cube R) :=
  (cube_isCompact R).measurableSet.map_coe_volume

def phaseMeasure (R : ℝ) : Measure (Phase R) :=
  (volume : Measure SpatialTorus).prod (momentumMeasure R)

instance phaseMeasure_finite (R : ℝ) : IsFiniteMeasure (phaseMeasure R) :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure SpatialTorus).prod (momentumMeasure R)))

theorem characteristic_preserves_measure (R t : ℝ) :
    MeasurePreserving (characteristic (R := R) t) (phaseMeasure R) (phaseMeasure R) := by
  let shift : MomentumDomain R → SpatialTorus :=
    fun k j => ((2*t*(k:E) j : ℝ) : AddCircle period)
  have hm : Measurable (fun q : MomentumDomain R × SpatialTorus => q.2 - shift q.1) := by
    apply Continuous.measurable
    apply continuous_pi
    intro j
    fun_prop
  have hs := (MeasurePreserving.id (momentumMeasure R)).skew_product
    (g := fun k x => x - shift k) hm
    (Filter.Eventually.of_forall fun k =>
      (measurePreserving_sub_right (volume : Measure SpatialTorus) (shift k)).map_eq)
  have h := Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)
  exact h

def characteristicHomeomorph (R t : ℝ) : Phase R ≃ₜ Phase R where
  toFun := characteristic t
  invFun := characteristic (-t)
  left_inv p := by rw [characteristic_add,neg_add_cancel,characteristic_zero]
  right_inv p := by rw [characteristic_add,add_neg_cancel,characteristic_zero]
  continuous_toFun := characteristic_continuous R t
  continuous_invFun := characteristic_continuous R (-t)

theorem transport_integral (R t : ℝ) (f : Distribution R) :
    ∫ p, transport R t f p ∂phaseMeasure R = ∫ p, f p ∂phaseMeasure R :=
  (characteristic_preserves_measure R t).integral_comp
    (characteristicHomeomorph R t).toMeasurableEquiv.measurableEmbedding f

theorem continuous_integrable (R : ℝ) (f : Distribution R) :
    Integrable f (phaseMeasure R) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

def integralLinear (R : ℝ) : Distribution R →ₗ[ℝ] ℝ where
  toFun f := ∫ p, f p ∂phaseMeasure R
  map_add' f g := integral_add (continuous_integrable R f) (continuous_integrable R g)
  map_smul' a f := integral_smul a f

def integralCLM (R : ℝ) : Distribution R →L[ℝ] ℝ :=
  (integralLinear R).mkContinuous (phaseMeasure R univ).toReal (fun f => by
    change ‖∫ p, f p ∂phaseMeasure R‖ ≤ (phaseMeasure R univ).toReal * ‖f‖
    simpa only [Measure.real,mul_comm] using
      norm_integral_le_of_norm_le_const (μ := phaseMeasure R) (C := ‖f‖)
        (Filter.Eventually.of_forall f.norm_coe_le_norm))

def quadratic (R : ℝ) (w f : Distribution R) : ℝ :=
  (1/2:ℝ) * integralCLM R (w * (f*f))

theorem quadratic_integral (R : ℝ) (w f : Distribution R) :
    quadratic R w f = (1/2:ℝ) * ∫ p, w p * (f p)^2 ∂phaseMeasure R := by
  change (1/2:ℝ) * (∫ p, w p * (f p*f p) ∂phaseMeasure R) = _
  simp only [pow_two]

theorem transport_mul (R t : ℝ) (f g : Distribution R) :
    transport R t (f*g) = transport R t f * transport R t g := rfl

theorem quadratic_transport (R t : ℝ) (w f : Distribution R) :
    quadratic R (transport R t w) (transport R t f) = quadratic R w f := by
  unfold quadratic
  rw [← transport_mul,← transport_mul]
  exact congrArg (fun x : ℝ => (1/2:ℝ)*x) (transport_integral R t (w*(f*f)))

theorem triple_transport (R t : ℝ) (w f g : Distribution R) :
    integralCLM R (transport R t w * (transport R t f * transport R t g)) =
      integralCLM R (w*(f*g)) := by
  rw [←transport_mul,←transport_mul]
  exact transport_integral R t (w*(f*g))

theorem triple_moving_to_physical (R t : ℝ) (w f g : Distribution R) :
    integralCLM R (transport R (-t) w * (f * transport R (-t) g)) =
      integralCLM R (w*(transport R t f*g)) := by
  have h := triple_transport R t (transport R (-t) w) f (transport R (-t) g)
  rw [transport_add_time,transport_add_time,add_neg_cancel,transport_zero,transport_zero] at h
  exact h.symm

theorem quadratic_moving_to_physical (R t : ℝ) (w f : Distribution R) :
    quadratic R (transport R (-t) w) f = quadratic R w (transport R t f) := by
  have h := quadratic_transport R t (transport R (-t) w) f
  rw [transport_add_time,add_neg_cancel,transport_zero] at h
  exact h.symm

theorem quadratic_nonneg (R : ℝ) (w f : Distribution R) (hw : ∀ p,0 ≤ w p) :
    0 ≤ quadratic R w f := by
  rw [quadratic_integral]
  apply mul_nonneg (by norm_num)
  exact integral_nonneg (fun p => mul_nonneg (hw p) (sq_nonneg _))

/-- The weight is differentiated in the same Banach space as the distribution.
This formula retains the full time-dependent weight contribution. -/
theorem quadratic_hasDerivWithinAt (R : ℝ) {s : Set ℝ} {t : ℝ}
    {w f : ℝ → Distribution R} {w' f' : Distribution R}
    (hw : HasDerivWithinAt w w' s t) (hf : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun τ => quadratic R (w τ) (f τ))
      ((1/2:ℝ)*integralCLM R (w'*(f t*f t)) +
        integralCLM R (w t*(f t*f'))) s t := by
  have h := ((integralCLM R).hasFDerivAt.comp_hasDerivWithinAt t
    (hw.mul (hf.mul hf))).const_mul (1/2:ℝ)
  have he : (1/2:ℝ)*integralCLM R
      (w'*(f t*f t)+w t*(f'*f t+f t*f')) =
      (1/2:ℝ)*integralCLM R (w'*(f t*f t))+
        integralCLM R (w t*(f t*f')) := by
    have hr : w t*(f'*f t+f t*f') = (2:ℝ) • (w t*(f t*f')) := by
      ext p
      simp only [ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,
        smul_eq_mul]
      ring
    rw [hr,map_add,map_smul]
    simp only [smul_eq_mul]
    ring
  exact he ▸ h

end
end Resonance.PhaseEnergy

#check Resonance.PhaseEnergy.momentumMeasure_mass
#print axioms Resonance.PhaseEnergy.momentumMeasure_mass
#check Resonance.PhaseEnergy.momentumMeasure_map
#print axioms Resonance.PhaseEnergy.momentumMeasure_map
#check Resonance.PhaseEnergy.characteristic_preserves_measure
#print axioms Resonance.PhaseEnergy.characteristic_preserves_measure
#check Resonance.PhaseEnergy.transport_integral
#print axioms Resonance.PhaseEnergy.transport_integral
#check Resonance.PhaseEnergy.continuous_integrable
#print axioms Resonance.PhaseEnergy.continuous_integrable
#check Resonance.PhaseEnergy.quadratic_integral
#print axioms Resonance.PhaseEnergy.quadratic_integral
#check Resonance.PhaseEnergy.transport_mul
#print axioms Resonance.PhaseEnergy.transport_mul
#check Resonance.PhaseEnergy.quadratic_transport
#print axioms Resonance.PhaseEnergy.quadratic_transport
#check Resonance.PhaseEnergy.triple_transport
#print axioms Resonance.PhaseEnergy.triple_transport
#check Resonance.PhaseEnergy.triple_moving_to_physical
#print axioms Resonance.PhaseEnergy.triple_moving_to_physical
#check Resonance.PhaseEnergy.quadratic_moving_to_physical
#print axioms Resonance.PhaseEnergy.quadratic_moving_to_physical
#check Resonance.PhaseEnergy.quadratic_nonneg
#print axioms Resonance.PhaseEnergy.quadratic_nonneg
#check Resonance.PhaseEnergy.quadratic_hasDerivWithinAt
#print axioms Resonance.PhaseEnergy.quadratic_hasDerivWithinAt
