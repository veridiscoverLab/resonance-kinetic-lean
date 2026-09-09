import Resonance.NormalizedParameterAlgebra

/-! The exact signed normalized kernel has an operator-compatible
parameter envelope, against the original reference-frequency rows. -/
open MeasureTheory Set
namespace Resonance.NormalizedPairParameterBounds
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure WeightedJointMeasure Thermodynamics CollisionFrequency JointWeightComparison
open PairParameterBounds NormalizedParameterAlgebra

def baseDensity (R : ℝ) (k p : E) : ℝ :=
  (IncomingPairDensity.density R (weight unitParameter) (k,p)).toReal+
    2*(CrossPairDensity.density R (weight unitParameter) (k,p)).toReal

theorem baseDensity_nonnegative (R : ℝ) (k p : E) : 0≤baseDensity R k p := by
  unfold baseDensity
  positivity

theorem compact_kernel_geometric_bound {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ∈K,∀β∈K,∀k∈cube R,∀p∈cube R,
      0<geometricFrequency R p →
      |AmbientLinftyCompact.kernel R θ k p-AmbientLinftyCompact.kernel R β k p|≤
        C*‖θ-β‖*(baseDensity R k p/geometricFrequency R p) := by
  obtain ⟨A,Cd,hA,hCd,hden,hdend⟩ := compact_denominator_bounds hR hK hpos
  obtain ⟨B,hB,hb⟩ := compact_pair_upper_bound hR hK hpos
  obtain ⟨Cr,hCr,hρ⟩ := compact_pair_difference_bound hR hK hpos
  let C := Cr/A+B*Cd/A^2
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro θ hθ β hβ k hk p hp hg
  have h1 := weighted_quotient_difference hA hg ENNReal.toReal_nonneg (norm_nonneg (θ-β))
    hCr hB hCd (hden θ hθ k hk p hp) (hden β hβ k hk p hp)
    (hρ θ hθ β hβ (k,p)).1
    (by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact (hb β hβ (k,p)).1)
    (hdend θ hθ β hβ k hk p hp)
  have h2 := weighted_quotient_difference hA hg ENNReal.toReal_nonneg (norm_nonneg (θ-β))
    hCr hB hCd (hden θ hθ k hk p hp) (hden β hβ k hk p hp)
    (hρ θ hθ β hβ (k,p)).2
    (by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact (hb β hβ (k,p)).2)
    (hdend θ hθ β hβ k hk p hp)
  change |(IncomingPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p-
      2*((CrossPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p)-
      ((IncomingPairDensity.density R (weight β) (k,p)).toReal/normalDenominator R β k p-
      2*((CrossPairDensity.density R (weight β) (k,p)).toReal/normalDenominator R β k p))|≤_
  have halg (a b c d : ℝ) : (a-2*b)-(c-2*d)=(a-c)-2*(b-d) := by ring
  rw [halg]
  calc
    _ ≤ |(IncomingPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p-
          (IncomingPairDensity.density R (weight β) (k,p)).toReal/normalDenominator R β k p|+
        |2*((CrossPairDensity.density R (weight θ) (k,p)).toReal/normalDenominator R θ k p-
          (CrossPairDensity.density R (weight β) (k,p)).toReal/normalDenominator R β k p)| :=
      abs_sub _ _
    _ ≤ C*‖θ-β‖*((IncomingPairDensity.density R (weight unitParameter) (k,p)).toReal/geometricFrequency R p)+
        2*(C*‖θ-β‖*((CrossPairDensity.density R (weight unitParameter) (k,p)).toReal/geometricFrequency R p)) := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by unfold baseDensity; ring

theorem geometric_inverse_comparison {R : ℝ} (hR : 0≤R) {p : E} (hp : p∈cube R)
    (hg : 0<geometricFrequency R p) {t : ℝ} (ht : 0≤t) :
    t/geometricFrequency R p≤(1+9*R^2)*(t/referenceFrequency R p) := by
  have h := referenceFrequency_geometric_bounds hR hp
  have hn : 0<referenceFrequency R p :=
    (mul_pos (pow_pos (inv_pos.mpr (by positivity : (0:ℝ)<1+9*R^2)) 3) hg).trans_le h.1
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hg hn).mpr
  calc
    t*referenceFrequency R p≤t*((1+9*R^2)*geometricFrequency R p) :=
      mul_le_mul_of_nonneg_left h.2 ht
    _ = _ := by ring

theorem compact_kernel_reference_bound {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ∈K,∀β∈K,∀k∈cube R,∀p∈cube R,
      0<geometricFrequency R p →
      |AmbientLinftyCompact.kernel R θ k p-AmbientLinftyCompact.kernel R β k p|≤
        C*‖θ-β‖*((referenceFrequency R p)⁻¹*baseDensity R k p) := by
  obtain ⟨C,hC,hb⟩ := compact_kernel_geometric_bound hR hK hpos
  refine ⟨C*(1+9*R^2),by positivity,?_⟩
  intro θ hθ β hβ k hk p hp hg
  calc
    _ ≤ C*‖θ-β‖*(baseDensity R k p/geometricFrequency R p) := hb θ hθ β hβ k hk p hp hg
    _ ≤ C*‖θ-β‖*((1+9*R^2)*(baseDensity R k p/referenceFrequency R p)) :=
      mul_le_mul_of_nonneg_left (geometric_inverse_comparison hR hp hg (baseDensity_nonnegative R k p))
        (mul_nonneg hC (norm_nonneg _))
    _ = _ := by ring

end
end Resonance.NormalizedPairParameterBounds
