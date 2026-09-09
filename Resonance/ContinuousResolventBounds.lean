import Resonance.RegularizedGraphNorm

/-! The actual continuous regularized inverse, with both norm estimates
uniform over a compact positive parameter set and every s ≥ 1. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousResolventBounds
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics WeightedJointMeasure
open ContinuousRegularizedEquation CubeLinftyCoordinates CubeContinuousEssentialNorm
open RegularizedCellBounds OneWeightedPairReadout ActualPairNormalization

theorem output_sub {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F G : C(cube R,ℝ)) :
    output hR hθ hs (F-G)=output hR hθ hs F-output hR hθ hs G := by
  apply (embedIsometry hR).injective
  change embed R _=embed R _
  rw [map_sub,output_embed,output_embed,output_embed,map_sub,map_sub]

theorem output_zero {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) : output hR hθ hs 0=0 := by
  apply (embedIsometry hR).injective
  change embed R _=embed R _
  simp only [output_embed,map_zero]

theorem output_ae_scaled {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F : C(cube R,ℝ)) :
    zeroExtension R (output hR hθ hs F)=ᵐ[cubeVolume R] fun k=>
      s⁻¹*ShiftedStrongCell.shiftedCell hR hθ (inv_nonneg.mpr hs.le) (embed R F) k := by
  have he := embed_ae R (output hR hθ hs F)
  rw [output_embed] at he
  exact he.symm.trans (boundedOutput_ae hR hθ _ _)

theorem actual_continuous_two_norm_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀θ,(hθ : θ∈K) → ∀s,(hs : 1 ≤ s) → ∀F : C(cube R,ℝ),
      ‖output hR (hpos hθ) (zero_lt_one.trans_le hs) F‖≤C*‖F‖ ∧
      s*‖referenceContinuous hR.le*output hR (hpos hθ) (zero_lt_one.trans_le hs) F‖≤C*‖F‖ := by
  obtain ⟨C,hC,hb⟩ := compact_shifted_cell_two_norm_bound hR hK hpos (Z:=1) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro θ hθ s hs F
  have hs0 : 0<s := zero_lt_one.trans_le hs
  have hz : s⁻¹∈Icc (0:ℝ) 1 := ⟨inv_nonneg.mpr hs0.le,inv_le_one_of_one_le₀ hs⟩
  obtain ⟨_hu,hq,_hw,hwb⟩ := hb θ hθ s⁻¹ hz (embed R F)
  refine ⟨?_,?_⟩
  · rw [←embed_norm_eq hR,output_embed]
    exact hq.trans (mul_le_mul_of_nonneg_left (extendVector_bound R F) hC.le)
  · have hsmall : ‖referenceContinuous hR.le*output hR (hpos hθ) hs0 F‖≤(C/s)*‖F‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      apply continuous_ae_bound hR
      filter_upwards [output_ae_scaled hR (hpos hθ) hs0 F,hwb,
        ae_restrict_mem (measurable_cube R)] with k he hw hk
      rw [zeroExtension_apply R _ ⟨k,hk⟩] at he ⊢
      change ‖CollisionFrequency.referenceFrequency R k*output hR (hpos hθ) hs0 F ⟨k,hk⟩‖≤_
      rw [he,mul_left_comm (CollisionFrequency.referenceFrequency R k) s⁻¹,
        norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
      calc
        _ ≤ s⁻¹*(C*‖embed R F‖) := mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hs0.le)
        _ ≤ s⁻¹*(C*‖F‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (extendVector_bound R F) hC.le) (inv_nonneg.mpr hs0.le)
        _=_ := by ring
    exact (mul_le_mul_of_nonneg_left hsmall hs0.le).trans_eq (by field_simp [hs0.ne'])

theorem actual_graph_resolvent_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀θ,(hθ : θ∈K) → ∀s,(hs : 1 ≤ s) → ∀F : C(cube R,ℝ),
      ‖RegularizedGraphNorm.lift hR.le s
        (output hR (hpos hθ) (zero_lt_one.trans_le hs) F)‖≤C*‖F‖ := by
  obtain ⟨C,hC,hb⟩ := actual_continuous_two_norm_bound hR hK hpos
  refine ⟨C,hC,?_⟩
  intro θ hθ s hs F
  exact RegularizedGraphNorm.norm_lift_le hR.le (zero_le_one.trans hs) _
    (hb θ hθ s hs F).1 (hb θ hθ s hs F).2

end
end Resonance.ContinuousResolventBounds
