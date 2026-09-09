import Resonance.PhysicalFrequencyCoordinates

/-! Uniform coordinate bounds obtained from actual pointwise profile
bounds, independent of the canonical domination constants used to
construct the maps. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.PhysicalFrequencyBounds
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics FrequencyWeightedForm
open ReferenceFrequencySpace ReferenceMarginalTransport PhysicalFrequencyCoordinates LpOperators

theorem multiply_explicit_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w : X→ℝ} (hw : MemLp w ∞ μ) {M : ℝ}
    (hb : ∀ᵐx∂μ,‖w x‖≤M) (f : Lp ℝ 2 μ) : ‖multiply hw f‖≤M*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae hw f,hb] with x hx hb
  rw [hx,norm_mul]
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem toReference_explicit_bound {R m : ℝ} (hR : 0≤R) (hm : 0 < m)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (hb : ∀k∈cube R,m≤profile θ k)
    (f : H R θ) : ‖toReference hR hθ f‖≤changeNorm (toReferenceFactor R m)*‖f‖ := by
  have he : toReference hR hθ f=
      changeMeasure (toReferenceFactor_finite R hm) (reference_le_actual hR hm hb) f := by
    apply Lp.ext
    exact (toReference_ae hR hθ f).trans (changeMeasure_ae
      (toReferenceFactor_finite R hm) (reference_le_actual hR hm hb) f).symm
  rw [he]
  exact changeMeasure_bound _ _ f

theorem backward_uniform_bound {R m M : ℝ} (hR : 0≤R) (hm : 0 < m) (hM : 0≤M)
    {θ : Parameter} (hθ : θ∈positiveDomain R)
    (hb : ∀k∈cube R,m≤profile θ k ∧ profile θ k≤M) (f : H R θ) :
    ‖backward hR hθ f‖≤(M*changeNorm (toReferenceFactor R m))*‖f‖ := by
  have hp : ∀ᵐk∂referenceMeasure R,‖profile θ k‖≤M := by
    filter_upwards [reference_support R] with k hk
    rw [Real.norm_eq_abs,abs_of_pos (profile_pos hθ hk)]
    exact (hb k hk).2
  change ‖multiply (profile_memLp_reference hθ) (toReference hR hθ f)‖≤_
  calc
    _ ≤ M*‖toReference hR hθ f‖ := multiply_explicit_bound _ hp _
    _ ≤ M*(changeNorm (toReferenceFactor R m)*‖f‖) := mul_le_mul_of_nonneg_left
      (toReference_explicit_bound hR hm hθ (fun k hk=>(hb k hk).1) f) hM
    _ = _ := (mul_assoc _ _ _).symm

end
end Resonance.PhysicalFrequencyBounds
