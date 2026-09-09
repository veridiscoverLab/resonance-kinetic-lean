import Resonance.PhysicalWeightedCoercivity

/-! Uniform upper bounds for the same complete form in the fixed reference
space, paid by the actual measure and profile comparisons. -/
open MeasureTheory
namespace Resonance.PhysicalFormUniformBounds
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics FrequencyWeightedForm
open ReferenceFrequencySpace ReferenceMarginalTransport PhysicalFrequencyCoordinates
open PhysicalFrequencyBounds LpOperators PhysicalWeightedCoercivity JointWeightComparison

theorem toMarginal_explicit_bound {R M : ℝ} (hR : 0≤R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) (hb : ∀k∈cube R,profile θ k≤M)
    (f : Space R) : ‖toMarginal hR hθ f‖≤changeNorm (toMarginalFactor R M)*‖f‖ := by
  have he : toMarginal hR hθ f=
      changeMeasure (toMarginalFactor_finite R M) (actual_le_reference hR hθ hb) f := by
    apply Lp.ext
    exact (toMarginal_ae hR hθ f).trans (changeMeasure_ae
      (toMarginalFactor_finite R M) (actual_le_reference hR hθ hb) f).symm
  rw [he]
  exact changeMeasure_bound _ _ f

theorem forward_uniform_bound {R m M : ℝ} (hR : 0≤R) (hm : 0 < m)
    {θ : Parameter} (hθ : θ∈positiveDomain R)
    (hb : ∀k∈cube R,m≤profile θ k ∧ profile θ k≤M) (u : Space R) :
    ‖forward hR hθ u‖≤(changeNorm (toMarginalFactor R M)*m⁻¹)*‖u‖ := by
  have hp : ∀ᵐk∂referenceMeasure R,‖(profile θ k)⁻¹‖ ≤ m⁻¹ := by
    filter_upwards [reference_support R] with k hk
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (profile_pos hθ hk))]
    exact inv_anti₀ hm (hb k hk).1
  change ‖toMarginal hR hθ (multiply (reciprocal_memLp_reference hR hθ) u)‖≤_
  calc
    _ ≤ changeNorm (toMarginalFactor R M)*‖multiply (reciprocal_memLp_reference hR hθ) u‖ :=
      toMarginal_explicit_bound hR hθ (fun k hk=>(hb k hk).2) _
    _ ≤ changeNorm (toMarginalFactor R M)*(m⁻¹*‖u‖) := mul_le_mul_of_nonneg_left
      (multiply_explicit_bound _ hp u) (by unfold changeNorm; positivity)
    _ = _ := (mul_assoc _ _ _).symm

theorem physical_form_uniform_upper {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ,(hθ : θ∈K) → ∀u : Space R,
      physicalForm hR.le (hpos hθ) u u≤C*‖u‖^2 := by
  obtain ⟨m,M,hm,_hM,hb⟩ := compact_profile_bounds hR.le hK hpos
  let a := 2*(changeNorm (toMarginalFactor R M)*m⁻¹)
  refine ⟨a^2,sq_nonneg _,?_⟩
  intro θ hθ u
  rw [physical_form_square]
  have ht : ‖physicalDifference hR.le (hpos hθ) u‖≤a*‖u‖ := by
    exact (fullDifference_bound R θ _).trans ((mul_le_mul_of_nonneg_left
      (forward_uniform_bound hR.le hm (hpos hθ) (hb θ hθ) u) (by norm_num)).trans_eq
        (by dsimp [a]; ring))
  have hs := mul_self_le_mul_self (norm_nonneg _) ht
  nlinarith

end
end Resonance.PhysicalFormUniformBounds
