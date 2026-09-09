import Resonance.UniformOnsagerResponse
import Resonance.EffectiveGradientNorm

/-! The parameter-uniform quantitative assertion in the paper's Onsager
kernel theorem, with its original tensor and Frobenius norm. -/
open Set
namespace Resonance.ActualOnsagerUniform
noncomputable section
open Thermodynamics ActualOnsagerTensor ActualOnsagerPositive
open UniformOnsagerResponse EffectiveGradientSpace EffectiveGradientNorm DeviatoricRankOne

theorem original_deviatoric_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K ⊆ positiveDomain R) :
    ∃a A : ℝ,0 < a ∧ 0 < A ∧ ∀θ : K,∀g h : Fin 3→ℝ,∀B : Fin 3→Fin 3→ℝ,
      a*(frobeniusSq (deviatoric B)+normSq h) ≤
        quadraticResponse hR (hpos θ.property) (OnsagerGradientPolynomial.gradient g B h) ∧
      quadraticResponse hR (hpos θ.property) (OnsagerGradientPolynomial.gradient g B h) ≤
        A*(frobeniusSq (deviatoric B)+normSq h) := by
  obtain ⟨a,A,ha,hA,hb⟩ := actual_quotient_bounds hR hK hpos
  refine ⟨a/8,3*A,by positivity,by positivity,?_⟩
  intro θ g h B
  have hq := hb θ (OnsagerGradientPolynomial.gradient g B h)
  have he := effective_energy_norm_bounds
    (observation (OnsagerGradientPolynomial.gradient g B h))
  rw [original_gradient_energy] at he
  constructor
  · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr he.2)]
  · nlinarith [mul_nonneg hA.le (sub_nonneg.mpr he.1)]

theorem original_rank_one_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K ⊆ positiveDomain R) :
    ∃a A : ℝ,0 < a ∧ 0 < A ∧ ∀θ : K,∀ell b : Fin 3→ℝ,∀d : ℝ,
      a*normSq ell*(normSq b+d^2) ≤
        quadraticResponse hR (hpos θ.property)
          (OnsagerGradientPolynomial.gradient (fun _=>0)
            (fun i j=>ell i*b j) (fun i=>ell i*d)) ∧
      quadraticResponse hR (hpos θ.property)
          (OnsagerGradientPolynomial.gradient (fun _=>0)
            (fun i j=>ell i*b j) (fun i=>ell i*d)) ≤
        A*normSq ell*(normSq b+d^2) := by
  obtain ⟨a,A,ha,hA,hb⟩ := original_deviatoric_bounds hR hK hpos
  refine ⟨a/2,A,by positivity,hA,?_⟩
  intro θ ell b d
  have hh := hb θ (fun _=>0) (fun i=>ell i*d) (fun i j=>ell i*b j)
  rw [rank_one_energy_norm] at hh
  have hl := rank_one_lower ell b
  have hu := rank_one_upper ell b
  have hnell : 0 ≤ normSq ell := Finset.sum_nonneg fun i _=>sq_nonneg _
  have hnb : 0 ≤ normSq b := Finset.sum_nonneg fun i _=>sq_nonneg _
  constructor
  · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hl),
      mul_nonneg ha.le (mul_nonneg hnell (sq_nonneg d))]
  · nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hu),
      mul_nonneg hA.le (mul_nonneg hnell hnb)]

end
end Resonance.ActualOnsagerUniform
