import Resonance.LinftyFiveAugmentation

/-! Quantitative dependence of the actual five-parameter RJ profile on
the fixed closed cube. No near-constant restriction is imposed. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Resonance.ProfileParameterBounds
noncomputable section
set_option maxHeartbeats 900000
open ResonantMeasure WeightedJointMeasure Thermodynamics PhysicalFiveBasis
open CoareaNormalization (euclideanFive euclideanFive_continuous)

def invariantContinuous (R : ℝ) (i : Fin 5) : C(cube R,ℝ) :=
  ⟨fun k=>euclideanFive i k,(euclideanFive_continuous i).comp continuous_subtype_val⟩

def denominatorMap (R : ℝ) : Parameter→L[ℝ]C(cube R,ℝ) :=
  ∑i : Fin 5,(ContinuousLinearMap.proj i).smulRight (invariantContinuous R i)

theorem denominatorMap_apply (R : ℝ) (θ : Parameter) (k : cube R) :
    denominatorMap R θ k=Entropy.denominator Entropy.fiveInvariants θ (coordinates k) := by
  simp only [denominatorMap,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,invariantContinuous,
    ContinuousMap.coe_mk,Entropy.denominator]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact CoareaNormalization.euclideanFive_coordinate i (coordinates k)

theorem denominator_difference_bound (R : ℝ) (θ β : Parameter) {k : E} (hk : k∈cube R) :
    |Entropy.denominator Entropy.fiveInvariants θ (coordinates k)-
      Entropy.denominator Entropy.fiveInvariants β (coordinates k)|≤
      ‖denominatorMap R‖*‖θ-β‖ := by
  rw [←denominatorMap_apply R θ ⟨k,hk⟩,←denominatorMap_apply R β ⟨k,hk⟩]
  change ‖(denominatorMap R θ-denominatorMap R β) ⟨k,hk⟩‖≤_
  rw [←map_sub]
  exact ((denominatorMap R (θ-β)).norm_coe_le_norm ⟨k,hk⟩).trans
    ((denominatorMap R).le_opNorm (θ-β))

theorem profile_difference_identity {R : ℝ} {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) {k : E} (hk : k∈cube R) :
    profile θ k-profile β k=profile θ k*profile β k*
      (Entropy.denominator Entropy.fiveInvariants β (coordinates k)-
        Entropy.denominator Entropy.fiveInvariants θ (coordinates k)) := by
  have hqθ := (hθ _ ((coordinates_cube R k).mp hk)).ne'
  have hqβ := (hβ _ ((coordinates_cube R k).mp hk)).ne'
  unfold profile Entropy.rj
  field_simp

theorem profile_difference_bound {R M : ℝ} {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R)
    (hM : 0≤M) (hθM : ∀k∈cube R,profile θ k≤M) (hβM : ∀k∈cube R,profile β k≤M)
    {k : E} (hk : k∈cube R) :
    |profile θ k-profile β k|≤M^2*‖denominatorMap R‖*‖θ-β‖ := by
  rw [profile_difference_identity hθ hβ hk,abs_mul,abs_mul,
    abs_of_pos (profile_pos hθ hk),abs_of_pos (profile_pos hβ hk),abs_sub_comm]
  calc
    _ ≤ (M*M)*(‖denominatorMap R‖*‖θ-β‖) :=
      mul_le_mul (mul_le_mul (hθM k hk) (hβM k hk) (profile_pos hβ hk).le hM)
        (denominator_difference_bound R θ β hk) (abs_nonneg _)
        (mul_nonneg hM hM)
    _ = _ := by ring

theorem compact_profile_lipschitz {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃m M C : ℝ,0 < m ∧ 0 < M ∧ 0 ≤ C ∧
      (∀θ∈K,∀k∈cube R,m≤profile θ k ∧ profile θ k≤M) ∧
      ∀θ∈K,∀β∈K,∀k∈cube R,|profile θ k-profile β k|≤C*‖θ-β‖ := by
  obtain ⟨m,M,hm,hM,hb⟩ := JointWeightComparison.compact_profile_bounds hR hK hpos
  refine ⟨m,M,M^2*‖denominatorMap R‖,hm,hM,by positivity,hb,?_⟩
  intro θ hθ β hβ k hk
  exact profile_difference_bound (hpos hθ) (hpos hβ) hM.le
    (fun k hk=>(hb θ hθ k hk).2) (fun k hk=>(hb β hβ k hk).2) hk

end
end Resonance.ProfileParameterBounds
