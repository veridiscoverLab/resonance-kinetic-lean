import Resonance.LinftyParameterContinuity

/-! The singular multiplication by one actual loss frequency has a
continuous operator family L-infinity -> H_nu on the fixed spaces. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.DivideParameterContinuity
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace ReferenceMomentFunctionals
open LinftyPhysicalDomain FrequencyParameterBounds NormalizedParameterAlgebra
open NormalizedPairParameterBounds LinftyParameterContinuity

theorem compact_inverse_loss_difference_bound {R : ℝ} (hR : 0≤R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ∈K,∀β∈K,∀k∈cube R,0<geometricFrequency R k →
      |(lossFrequency R (profile θ) k)⁻¹-(lossFrequency R (profile β) k)⁻¹|≤
        C*‖θ-β‖*(referenceFrequency R k)⁻¹ := by
  obtain ⟨a,b,C,ha,hb,hC,hl,hd⟩ := compact_loss_difference_bound hR hK hpos
  refine ⟨(C/a^2)*(1+9*R^2),by positivity,?_⟩
  intro θ hθ β hβ k hk hg
  have he := quotient_difference_bound (mul_pos ha hg) (hl θ hθ k hk).1
    (hl β hβ k hk).1 (r:=1) (s:=1)
  simp only [one_div,sub_self,abs_zero,zero_div,zero_add,abs_one,one_mul] at he
  calc
    _ ≤ |lossFrequency R (profile θ) k-lossFrequency R (profile β) k|/
        (a*geometricFrequency R k)^2 := he
    _ ≤ (C*‖θ-β‖*geometricFrequency R k)/(a*geometricFrequency R k)^2 :=
      div_le_div_of_nonneg_right (hd θ hθ β hβ k hk) (sq_nonneg _)
    _ = (C/a^2)*‖θ-β‖*(1/geometricFrequency R k) := by field_simp
    _ ≤ (C/a^2)*‖θ-β‖*((1+9*R^2)*(1/referenceFrequency R k)) :=
      mul_le_mul_of_nonneg_left (geometric_inverse_comparison hR hk hg zero_le_one) (by positivity)
    _ = _ := by ring

theorem compact_divide_difference_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀(θ : Parameter)(hθ : θ∈K)(β : Parameter)(hβ : β∈K),
      ‖divide hR (hpos hθ)-divide hR (hpos hβ)‖≤C*‖θ-β‖ := by
  obtain ⟨C,hC,hb⟩ := compact_inverse_loss_difference_bound hR.le hK hpos
  refine ⟨C*‖inverseVector hR‖,by positivity,?_⟩
  intro θ hθ β hβ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hh : ‖divide hR (hpos hθ) f-divide hR (hpos hβ) f‖≤
      (C*‖θ-β‖*‖f‖)*‖inverseVector hR‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [divideVector_ae hR (hpos hθ) f,divideVector_ae hR (hpos hβ) f,
      Lp.coeFn_sub (divide hR (hpos hθ) f) (divide hR (hpos hβ) f),
      inverseVector_ae hR,reference_support R,
      (reference_volume_equivalent hR).2.ae_le (geometricFrequency_positive_ae hR),
      (reference_volume_equivalent hR).2.ae_le (LinftyRowOperator.ae_norm_bound f)]
        with k h1 h2 hs hv hk hg hf
    simp only [Pi.sub_apply] at hs
    change (divide hR (hpos hθ) f) k=f k/lossFrequency R (profile θ) k at h1
    change (divide hR (hpos hβ) f) k=f k/lossFrequency R (profile β) k at h2
    rw [hs,h1,h2,hv,div_eq_mul_inv,div_eq_mul_inv,←mul_sub,norm_mul,
      Real.norm_eq_abs ((lossFrequency R (profile θ) k)⁻¹-(lossFrequency R (profile β) k)⁻¹),
      Real.norm_of_nonneg (show 0≤(referenceFrequency R k)⁻¹ from
        CrossRowWeightedBounds.inverseFrequency_nonnegative R k)]
    exact (mul_le_mul hf (hb θ hθ β hβ k hk hg) (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
  exact hh.trans_eq (by ring)

end
end Resonance.DivideParameterContinuity
