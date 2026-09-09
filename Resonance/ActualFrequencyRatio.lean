import Resonance.ActualReferenceRowOperator

/-! The frequency ratio is bounded by the actual positive RJ profile
and the actual geometric loss integral.  Its value at a zero-frequency
corner is the ordinary real inverse convention, and is not asserted to
be a continuous quotient. -/
open MeasureTheory Set
open scoped ENNReal Topology
namespace Resonance.ActualFrequencyRatio
noncomputable section
set_option maxHeartbeats 900000
open ResonantMeasure WeightedJointMeasure CollisionFrequency

theorem loss_reference_lower {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ a : ℝ, 0 < a ∧ ∀ k ∈ cube R,
      a*referenceFrequency R k ≤ lossFrequency R (profile θ) k := by
  obtain ⟨m,hm,hml⟩ := FrequencyWeightedKernel.profile_uniform_lower hR.le hθ
  obtain ⟨M,hM,hMu⟩ := profile_bounded hθ
  let B : ℝ := M+1
  have hB : 0 < B := by dsimp [B]; linarith
  let a : ℝ := (m^3/B)/(1+9*R^2)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a,ha,?_⟩
  intro k hk
  have hb (p : E) (hp : p ∈ cube R) : m ≤ profile θ p ∧ profile θ p ≤ B :=
    ⟨hml p hp,(le_abs_self _).trans ((hMu p hp).trans (by dsimp [B]; linarith))⟩
  calc
    a*referenceFrequency R k ≤ a*((1+9*R^2)*geometricFrequency R k) :=
      mul_le_mul_of_nonneg_left (referenceFrequency_geometric_bounds hR.le hk).2 ha.le
    _ = (m^3/B)*geometricFrequency R k := by dsimp [a]; field_simp
    _ ≤ _ := (lossFrequency_geometric_bounds hR.le hm hB (profile θ)
      (profile_measurable θ) hb hk).1

theorem loss_nonnegative {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    {k : E} (hk : k ∈ cube R) : 0 ≤ lossFrequency R (profile θ) k := by
  obtain ⟨a,ha,hb⟩ := loss_reference_lower hR hθ
  exact (mul_nonneg ha.le (CrossRowWeightedBounds.referenceFrequency_nonnegative R k)).trans (hb k hk)

def inputRatio (R : ℝ) (θ : Thermodynamics.Parameter) (p : E) : ℝ :=
  referenceFrequency R p/(profile θ p*lossFrequency R (profile θ) p)

theorem inputRatio_measurable (R : ℝ) (θ : Thermodynamics.Parameter) :
    Measurable (inputRatio R θ) :=
  (CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable).div
    ((profile_measurable θ).mul
      (CollisionMarginalDensity.lossFrequency_measurable R (profile_measurable θ)))

theorem inputRatio_bounded {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ cube R, ‖inputRatio R θ p‖ ≤ B := by
  obtain ⟨a,ha,hl⟩ := loss_reference_lower hR hθ
  obtain ⟨m,hm,hml⟩ := FrequencyWeightedKernel.profile_uniform_lower hR.le hθ
  refine ⟨(m*a)⁻¹,inv_pos.mpr (mul_pos hm ha),?_⟩
  intro p hp
  have hN := profile_pos hθ hp
  have hν := loss_nonnegative hR hθ hp
  have hνs := CrossRowWeightedBounds.referenceFrequency_nonnegative R p
  unfold inputRatio
  rw [Real.norm_of_nonneg (div_nonneg hνs (mul_nonneg hN.le hν))]
  by_cases hz : lossFrequency R (profile θ) p=0
  · simp only [hz,mul_zero,div_zero]
    positivity
  · have hνp : 0 < lossFrequency R (profile θ) p := lt_of_le_of_ne hν (Ne.symm hz)
    apply (div_le_iff₀ (mul_pos hN hνp)).mpr
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ (mul_pos hm ha)).mpr
    calc
      _ = m*(a*referenceFrequency R p) := by ring
      _ ≤ m*lossFrequency R (profile θ) p := mul_le_mul_of_nonneg_left (hl p hp) hm.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (hml p hp) hν

def inverseProfile {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) : C(cube R,ℝ) :=
  ⟨fun k => (profile θ k)⁻¹,
    (continuousOn_iff_continuous_restrict.mp (FrequencyWeightedKernel.profile_continuousOn hθ)).inv₀
      (fun k => (profile_pos hθ k.property).ne')⟩

end
end Resonance.ActualFrequencyRatio
