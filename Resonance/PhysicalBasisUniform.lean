import Resonance.PhysicalProjectionUniform

/-! Uniform bounds for the original synthesis and unweighted moment
analysis maps on the complete weighted physical space. -/
open Set MeasureTheory
namespace Resonance.PhysicalBasisUniform
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000
open ResonantMeasure Thermodynamics ReferenceFrequencySpace PhysicalFiveBasis
open PhysicalMomentProjection PhysicalProjectionUniform PhysicalFrequencyBounds
open JointWeightComparison ReferenceMarginalTransport WeightedJointMeasure
open PhysicalFrequencyCoordinates

theorem compact_basis_operator_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃A S : ℝ,0 ≤ A ∧ 0 ≤ S ∧ ∀ θ,(hθ : θ∈K) →
      ‖analysisMap hR (hpos hθ)‖ ≤ A ∧ ‖synthesis hR.le (hpos hθ)‖ ≤ S := by
  obtain ⟨m,M,_hm,hM,hb⟩ := compact_profile_bounds hR.le hK hpos
  let A₀ := analysisMap hR (unitParameter_positive R)
  let S₀ := synthesis hR.le (unitParameter_positive R)
  refine ⟨‖A₀‖*M,M*‖S₀‖,by positivity,by positivity,?_⟩
  intro θ hθ
  have hmult (v : Space R) :
      ‖LpOperators.multiplyCLM (profile_memLp_reference (hpos hθ)) v‖ ≤ M*‖v‖ := by
    apply multiply_explicit_bound (profile_memLp_reference (hpos hθ)) ?_ v
    filter_upwards [reference_support R] with k hk
    rw [Real.norm_eq_abs,abs_of_pos (profile_pos (hpos hθ) hk)]
    exact (hb θ hθ k hk).2
  constructor
  · apply (analysisMap hR (hpos hθ)).opNorm_le_bound (by positivity)
    intro v
    rw [analysis_profile_factor]
    exact ((A₀.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hmult v) (norm_nonneg A₀))).trans_eq (by ring)
  · apply (synthesis hR.le (hpos hθ)).opNorm_le_bound (by positivity)
    intro a
    rw [synthesis_profile_factor]
    exact ((hmult (S₀ a)).trans
      (mul_le_mul_of_nonneg_left (S₀.le_opNorm a) hM.le)).trans_eq (by ring)

end
end Resonance.PhysicalBasisUniform
