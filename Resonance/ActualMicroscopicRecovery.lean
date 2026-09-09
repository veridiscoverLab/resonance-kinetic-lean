import Resonance.ContinuousMicroscopicMatching
import Resonance.ActualFullRecovery

/-! Full recovery for the actual reciprocal microscopic variable of the
same five-moment matched distribution, on the original sharp cube. -/
open Set
namespace Resonance.ActualMicroscopicRecovery
noncomputable section
open ResonantMeasure Thermodynamics ThermodynamicChart WeightedJointMeasure
open ProfileBanachSmooth ContinuousSourceCoordinates ContinuousSourceMultiplication
open ContinuousMicroscopicFields PhysicalFiveBasis ActualMatchedMoments
open ContinuousMicroscopicMatching ReferenceFrequencySpace PhysicalWeightedCoercivity
open PhysicalFrequencyCoordinates

theorem matchingWeight_bounds {f N Nc m M : ℝ} (hm : 0 < m)
    (hf : m ≤ f ∧ f ≤ M) (hN : m ≤ N ∧ N ≤ M) (hNc : m ≤ Nc ∧ Nc ≤ M) :
    m^2/M^2 ≤ MicroscopicCoordinates.matchingWeight f N Nc ∧
    MicroscopicCoordinates.matchingWeight f N Nc ≤ M^2/m^2 := by
  have hnp : 0<N := hm.trans_le hN.1
  have hmp : 0<M := hnp.trans_le hN.2
  have hprod : m^2≤f*Nc ∧ f*Nc≤M^2 := by
    constructor
    · calc m^2=m*m := pow_two m
           _ ≤ f*Nc := mul_le_mul hf.1 hNc.1 hm.le (hm.trans_le hf.1).le
    · calc f*Nc ≤ M*M := mul_le_mul hf.2 hNc.2 (hm.trans_le hNc.1).le hmp.le
           _ = M^2 := (pow_two M).symm
  unfold MicroscopicCoordinates.matchingWeight
  constructor
  · apply (div_le_div_of_nonneg_left (sq_nonneg m) (sq_pos_of_pos hnp)
      (pow_le_pow_left₀ hnp.le hN.2 2)).trans
    exact div_le_div_of_nonneg_right hprod.1 (sq_nonneg N)
  · apply (div_le_div_of_nonneg_right hprod.2 (sq_nonneg N)).trans
    exact div_le_div_of_nonneg_left (sq_nonneg M) (sq_pos_of_pos hm)
      (pow_le_pow_left₀ hm.le hN.1 2)

theorem actual_full_microscopic_recovery {R m M : ℝ} (hR : 0 < R)
    (hm : 0 < m) (hM : 0 ≤ M) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀ θ,(hθ : θ∈K) → ∀ c : ℝ,
    ∀ (f : FreeTransport.Distribution R) (X : FreeTransport.SpatialTorus),
    (∀ k,f (X,k)≠0) → (hX : actualMoments R f X∈momentImage R) →
    (∀ k,m≤bField (f.curry X) (profileMap R θ)
      (profileMap R (matchedValue R hR f X)) k ∧
      bField (f.curry X) (profileMap R θ) (profileMap R (matchedValue R hR f X)) k≤M) →
    ∀ u : Space R,analysisMap hR (hpos hθ) u=0 →
    let y := sourceMap hR (yField c (f.curry X) (profileMap R θ)
      (profileMap R (matchedValue R hR f X)))
    let B := multiplier hR (bField (f.curry X) (profileMap R θ)
      (profileMap R (matchedValue R hR f X)))
    ‖y-u‖^2≤C*(‖physicalDifference hR.le (hpos hθ) (y-u)‖^2+‖(B-1) u‖^2) := by
  obtain ⟨C,hC,hrec⟩ := ActualFullRecovery.original_full_recovery_bound hR hm hM hK hpos
  refine ⟨C,hC,?_⟩
  intro θ hθ c f X hf hX hbnd u hu
  exact hrec θ hθ _ (StrongBoundedCell.source_memLp_reference hR _) (multiplier_cube_bounds _ hbnd)
    _ u (actual_matched_weighted_constraint hR c f X hf hX (hpos hθ)) hu

end
end Resonance.ActualMicroscopicRecovery
