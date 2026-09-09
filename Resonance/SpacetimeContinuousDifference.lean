import Resonance.SpacetimeContinuousFields
import Resonance.ActualMicroscopicCurrent

/-! The common dynamic difference reads the same actual continuous cube
family used by the original collision equation. The identity is established
on all four original flags before taking joint a.e. representatives. -/
open Set MeasureTheory MeasureTheory.Measure
namespace Resonance.SpacetimeContinuousDifference
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing SpacetimeReference
open SpacetimeContinuousFields SpacetimeDifference WeightedJointMeasure
open ActualMicroscopicCurrent ProfileBanachSmooth FiberContinuity

theorem physicalRaw_field_point {R : ℝ} (F : Base→C(cube R,ℝ))
    (θ : Base→Parameter) (p : Joint) (hp : ∀i,p.2 i∈cube R) :
    physicalRaw (θ:=θ) (field F) p=
      halfDifference (denominatorMap R (θ p.1)*F p.1) p.2 := by
  change (1/2:ℝ)*Collision.delta (fun i=>field F (leg i p)/profile (θ p.1) (p.2 i))=_
  congr 1
  apply congrArg Collision.delta
  funext i
  rw [continuousExtension_eq R _ ⟨p.2 i,hp i⟩,ContinuousMap.mul_apply,
    denominatorMap_apply]
  change field F (p.1,p.2 i)/profile (θ p.1) (p.2 i)=_
  rw [show field F (p.1,p.2 i)=F p.1 ⟨p.2 i,hp i⟩ from field_on_cube F p.1 ⟨p.2 i,hp i⟩]
  rw [div_eq_mul_inv,profile_eq_inverse_denominator,inv_inv,mul_comm]

theorem physicalRaw_field_ae {R : ℝ} (T : ℝ) (F : Base→C(cube R,ℝ))
    (θ : Base→Parameter) :
    physicalRaw (θ:=θ) (field F)=ᵐ[SpacetimeRJMeasure.measure R T θ]
      (fun p=>halfDifference (denominatorMap R (θ p.1)*F p.1) p.2) := by
  filter_upwards [(SpacetimeRJMeasure.measure_absolutelyContinuous R T θ).ae_le
    (joint_full_support R T)] with p hp
  exact physicalRaw_field_point F θ p hp.1

theorem physicalDifference_source_ae {R : ℝ} (hR : 0<R) (T : ℝ)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R)
    {θ : Base→Parameter} (hm : Measurable θ) (hθ : ∀ᵐz∂baseMeasure T,θ z∈K)
    {F : Base→C(cube R,ℝ)} {C : ℝ} (hF : Measurable F)
    (hb : ∀ᵐz∂baseMeasure T,‖F z‖≤C) :
    physicalDifference hR T hK hpos hm hθ (source hR.le T hF hb)=ᵐ[SpacetimeRJMeasure.measure R T θ]
      (fun p=>halfDifference (denominatorMap R (θ p.1)*F p.1) p.2) := by
  have hu:=source_ae hR.le T hF hb
  have hr:=physicalDifference_ae hR T hK hpos hm hθ (source hR.le T hF hb)
  filter_upwards [hr,physicalRaw_field_ae T F θ,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 0).ae_eq hu,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 1).ae_eq hu,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 2).ae_eq hu,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 3).ae_eq hu]
    with p hr hp h0 h1 h2 h3
  rw [hr,←hp]
  simp only [Function.comp_def] at h0 h1 h2 h3
  simp only [physicalRaw,rawDifference,h0,h1,h2,h3]

end
end Resonance.SpacetimeContinuousDifference
