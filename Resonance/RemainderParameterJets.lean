import Resonance.CubicParameterJets
import Resonance.GraphResolventSmooth

/-! Full quadratic/cubic remainder parameter derivatives, with the
one-Y Lipschitz factor retained at every finite order. The nine terms
are the exact difference of the same four-parent collision polynomial. -/
open Set
open scoped ContDiff Topology BigOperators
namespace Resonance.RemainderParameterJets
noncomputable section
set_option maxHeartbeats 2600000
open ResonantMeasure Thermodynamics ProfileBanachSmooth NormalizedCubicOneY
open NormalizedCubicRemainder CubicParameterJets OneWeightedPairReadout

theorem normalized_fixed_inputs_contDiffAt {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Fin 3→X R) :
    ContDiffAt ℝ ∞ (fun β=>normalizedTrilinear R hR β u) θ := by
  have he : (fun β=>normalizedTrilinear R hR β u)=
      (fun β=>evaluationFamily R β (CubicParameterCoefficients.coefficientMap R hR u)) := by
    funext β
    exact (evaluationFamily_apply R hR β u).symm
  rw [he]
  exact (evaluationFamily_contDiffAt hθ).clm_apply contDiffAt_const

def differenceInputs {R : ℝ} (q r : X R) : Fin 9→(Fin 3→X R) :=
  ![![q-r,q,1],![r,q-r,1],![q-r,1,q],![r,1,q-r],![1,q-r,q],![1,r,q-r],
    ![q-r,q,q],![r,q-r,q],![r,r,q-r]]

theorem exact_parameter_difference {R : ℝ} (hR : 0≤R) (β : Parameter) (q r : X R) :
    remainder R hR β q-remainder R hR β r=
      ∑i : Fin 9,normalizedTrilinear R hR β (differenceInputs q r i) := by
  rw [remainder,remainder,TrilinearRemainderAlgebra.exact_difference]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> rfl

theorem product_small {L C w a b κ : ℝ} (hC : 0≤C) (hw : 0≤w)
    (h : L≤C*w*a*b) (hp : a*b≤κ) : L≤C*κ*w := by
  calc
    L≤(C*w)*(a*b) := h.trans_eq (by ring)
    _≤(C*w)*κ := mul_le_mul_of_nonneg_left hp (mul_nonneg hC hw)
    _=_ := by ring

theorem actual_remainder_parameter_jet_lipschitz {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀κ≤1,∀q r : X R,‖q‖≤κ → ‖r‖≤κ →
      ‖iteratedFDeriv ℝ n (fun β=>remainder R hR.le β q-remainder R hR.le β r) θ‖≤
        C*κ*‖referenceContinuous hR.le*(q-r)‖ := by
  obtain ⟨A,hA,ha⟩ := actual_normalized_cubic_parameter_jets hR hK hpos n
  refine ⟨9*A,by positivity,?_⟩
  intro θ hθ κ hκ q r hq hr
  have hκ0 : 0≤κ := (norm_nonneg q).trans hq
  have hq1 : ‖q‖*‖(1:X R)‖≤κ :=
    (mul_le_mul hq (one_norm_le R) (norm_nonneg _) hκ0).trans_eq (mul_one κ)
  have hr1 : ‖r‖*‖(1:X R)‖≤κ :=
    (mul_le_mul hr (one_norm_le R) (norm_nonneg _) hκ0).trans_eq (mul_one κ)
  have h1q : ‖(1:X R)‖*‖q‖≤κ := (mul_comm _ _).trans_le hq1
  have h1r : ‖(1:X R)‖*‖r‖≤κ := (mul_comm _ _).trans_le hr1
  have hκsq : κ*κ≤κ := (mul_le_mul_of_nonneg_left hκ hκ0).trans_eq (mul_one κ)
  have hqq : ‖q‖*‖q‖≤κ := (mul_le_mul hq hq (norm_nonneg _) hκ0).trans hκsq
  have hrq : ‖r‖*‖q‖≤κ := (mul_le_mul hr hq (norm_nonneg _) hκ0).trans hκsq
  have hrr : ‖r‖*‖r‖≤κ := (mul_le_mul hr hr (norm_nonneg _) hκ0).trans hκsq
  have hb : ∀i : Fin 9,
      ‖iteratedFDeriv ℝ n (fun β=>normalizedTrilinear R hR.le β (differenceInputs q r i)) θ‖≤
        A*κ*‖referenceContinuous hR.le*(q-r)‖ := by
    intro i
    fin_cases i
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![q-r,q,1]).1 hq1
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![r,q-r,1]).2.1 hr1
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![q-r,1,q]).1 h1q
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![r,1,q-r]).2.2 hr1
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![1,q-r,q]).2.1 h1q
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![1,r,q-r]).2.2 h1r
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![q-r,q,q]).1 hqq
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![r,q-r,q]).2.1 hrq
    · exact product_small hA.le (norm_nonneg _) (ha θ hθ ![r,r,q-r]).2.2 hrr
  have he : (fun β=>remainder R hR.le β q-remainder R hR.le β r)=
      (fun β=>∑i : Fin 9,normalizedTrilinear R hR.le β (differenceInputs q r i)) := by
    funext β
    exact exact_parameter_difference hR.le β q r
  rw [he,iteratedFDeriv_fun_sum_apply]
  · exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _=>hb i)).trans_eq (by simp; ring))
  · intro i _
    exact (normalized_fixed_inputs_contDiffAt hR.le (hpos hθ) _).of_le
      (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))

theorem actual_remainder_parameter_jet_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀κ≤1,∀q : X R,‖q‖≤κ →
      ‖iteratedFDeriv ℝ n (fun β=>remainder R hR.le β q) θ‖≤
        C*κ*‖referenceContinuous hR.le*q‖ := by
  obtain ⟨C,hC,hb⟩ := actual_remainder_parameter_jet_lipschitz hR hK hpos n
  refine ⟨C,hC,?_⟩
  intro θ hθ κ hκ q hq
  have hh := hb θ hθ κ hκ q 0 hq (by simpa using (norm_nonneg q).trans hq)
  simpa only [remainder_zero,sub_zero] using hh

end
end Resonance.RemainderParameterJets
