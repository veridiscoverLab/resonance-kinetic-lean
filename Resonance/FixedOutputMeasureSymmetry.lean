import Resonance.FixedOutputOutgoing
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Equality of the original finite conditional measures follows from
the proved continuous readouts, at every original cube output. -/
open Real Set MeasureTheory BoundedContinuousFunction
open scoped ENNReal NNReal BoundedContinuousFunction
namespace Resonance.FixedOutputMeasureSymmetry
noncomputable section
open ResonantMeasure CollisionFiber CollisionFrequency FiberContinuity
open MarkedFiberIsometry FixedOutputOutgoing
set_option maxHeartbeats 1200000

theorem original_fiber_isometry {R : ℝ} (hR : 0 ≤ R) (J : E ≃ₗᵢ[ℝ] E)
    (hJ : ∀x:E,J x∈cube R ↔ x∈cube R) (k : E) (hk : k∈cube R) :
    Measure.map (fun q : FourMomenta => fun l => J (q l)) (fiberMeasure R k) =
      fiberMeasure R (J k) := by
  let T : FourMomenta → FourMomenta := fun q l => J (q l)
  have hT : Continuous T := continuous_pi (fun l => J.continuous.comp (continuous_apply l))
  letI : IsFiniteMeasure (fiberMeasure R k) := ⟨geometricFrequency_mass_finite hR k⟩
  letI : IsFiniteMeasure (fiberMeasure R (J k)) := ⟨geometricFrequency_mass_finite hR (J k)⟩
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  rw [lintegral_map (f.continuous.measurable.coe_nnreal_ennreal) hT.measurable]
  let g : FourMomenta →ᵇ ℝ≥0 := f.compContinuous ⟨T,hT⟩
  change (∫⁻ q, (g q : ℝ≥0∞) ∂fiberMeasure R k) =
    ∫⁻ q, (f q : ℝ≥0∞) ∂fiberMeasure R (J k)
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal _ g).ne
    (lintegral_lt_top_of_nnreal _ f).ne).mp
  rw [toReal_lintegral_coe_eq_integral g _,toReal_lintegral_coe_eq_integral f _]
  exact (original_marked_fiber_isometry hR J hJ
    (NNReal.continuous_coe.comp f.continuous) (fun q => (f q).coe_nonneg) k hk).symm

theorem original_fiber_outgoing {R : ℝ} (hR : 0 < R) (k : E) (hk : k∈cube R) :
    Measure.map swapOutgoingK (fiberMeasure R k) = fiberMeasure R k := by
  letI : IsFiniteMeasure (fiberMeasure R k) := ⟨geometricFrequency_mass_finite hR.le k⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map swapOutgoingK_continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact original_continuous_outgoing hR f.continuous k hk

end
end Resonance.FixedOutputMeasureSymmetry
