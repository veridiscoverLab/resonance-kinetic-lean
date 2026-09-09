import Resonance.ContinuousMicroscopicFields
import Resonance.ActualMatchedMoments

/-! The weighted constraint is derived from the original five moments,
with no additional projection hypothesis on the microscopic variable. -/
open Set
namespace Resonance.ContinuousMicroscopicMatching
noncomputable section
open ResonantMeasure Thermodynamics ThermodynamicChart WeightedJointMeasure
open ProfileBanachSmooth ContinuousSourceCoordinates ContinuousSourceMultiplication
open ContinuousMicroscopicFields PhysicalFiveBasis ActualMatchedMoments

theorem profileMap_eq_rjCube {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    profileMap R θ=rjCube R θ hθ := by
  ext k
  exact profileMap_apply hθ k

theorem original_weighted_moments {R : ℝ} (hR : 0<R) (c : ℝ)
    (f : C(cube R,ℝ)) (hf : ∀ k,f k≠0) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    analysisMap hR hθ (multiplier hR (bField f (profileMap R θ) (profileMap R θc))
      (sourceMap hR (yField c f (profileMap R θ) (profileMap R θc))))=
      c • (moments R f-momentMap R θc) := by
  have hN : ∀ k,profileMap R θ k≠0 := by
    intro k
    rw [profileMap_apply hθ]
    exact ne_of_gt (profile_pos hθ k.property)
  have hNc : ∀ k,profileMap R θc k≠0 := by
    intro k
    rw [profileMap_apply hθc]
    exact ne_of_gt (profile_pos hθc k.property)
  rw [multiplier_sourceMap]
  ext i
  rw [analysis_source_embed,weighted_matching_field c f _ _ hf hN hNc]
  change ContinuousCollisionMoments.moment R (basisParameter i)
    (c • (f-profileMap R θc))=_
  rw [map_smul,map_sub,profileMap_eq_rjCube hθc]
  have hi := congrArg (fun a : Parameter=>a i) (rjCube_moments R θc hθc)
  change ContinuousCollisionMoments.moment R (basisParameter i) (rjCube R θc hθc)=_ at hi
  rw [hi]
  rfl

theorem actual_matched_weighted_constraint {R : ℝ} (hR : 0<R) (c : ℝ)
    (f : FreeTransport.Distribution R) (X : FreeTransport.SpatialTorus)
    (hf : ∀ k,f (X,k)≠0) (hX : actualMoments R f X∈momentImage R)
    {θ : Parameter} (hθ : θ∈positiveDomain R) :
    analysisMap hR hθ
      (multiplier hR (bField (f.curry X) (profileMap R θ)
        (profileMap R (matchedValue R hR f X)))
      (sourceMap hR (yField c (f.curry X) (profileMap R θ)
        (profileMap R (matchedValue R hR f X)))))=0 := by
  rw [original_weighted_moments hR c (f.curry X) hf hθ
    (matched_positive R hR f X hX),matchedValue,momentInverse_right R hR _ hX]
  change c • (actualMoments R f X-actualMoments R f X)=0
  rw [sub_self,smul_zero]

end
end Resonance.ContinuousMicroscopicMatching
