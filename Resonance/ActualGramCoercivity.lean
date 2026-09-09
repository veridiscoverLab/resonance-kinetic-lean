import Resonance.GramCoefficientContinuity
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Uniform positivity of the original five-moment Gram form in the
actual parameter norm. It will control the moving, unknown weighted
Gram matrix in the recovery of all five microscopic kernel coordinates. -/
open Set Matrix
namespace Resonance.ActualGramCoercivity
noncomputable section
open Thermodynamics GramCoefficientContinuity

def gramQuadratic (R : ℝ) (θ a : Parameter) : ℝ := a ⬝ᵥ (gramMatrix R θ).mulVec a

theorem gramQuadratic_continuousOn (R : ℝ) :
    ContinuousOn (fun z : Parameter×Parameter=>gramQuadratic R z.1 z.2)
      ((positiveDomain R)×ˢuniv) := by
  have hM := (original_gram_continuousOn R).comp continuous_fst.continuousOn
    (fun z (hz : z∈(positiveDomain R)×ˢ(univ : Set Parameter))=>hz.1)
  exact quadratic_continuous.comp_continuousOn (hM.prodMk continuous_snd.continuousOn)

theorem gramQuadratic_smul (R : ℝ) (θ a : Parameter) (r : ℝ) :
    gramQuadratic R θ (r • a)=r^2*gramQuadratic R θ a := by
  simp only [gramQuadratic,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

theorem compact_original_gram_lower {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃lam : ℝ,0 < lam ∧ ∀ θ∈K,∀ a : Parameter,lam*‖a‖^2 ≤ gramQuadratic R θ a := by
  let S : Set (Parameter×Parameter) := K×ˢMetric.sphere 0 1
  have hS : IsCompact S := hK.prod (isCompact_sphere (0 : Parameter) 1)
  have hcont : ContinuousOn (fun z : Parameter×Parameter=>gramQuadratic R z.1 z.2) S :=
    (gramQuadratic_continuousOn R).mono (fun _ hz=>⟨hpos hz.1,mem_univ _⟩)
  have hp : ∀ z∈S,0 < gramQuadratic R z.1 z.2 := by
    intro z hz
    have hn : z.2≠0 := by
      intro he
      simpa [he] using hz.2
    unfold gramQuadratic
    rw [gram_quadratic_identity R z.1 (hpos hz.1)]
    exact gram_quadratic_pos R hR z.1 (hpos hz.1) z.2 hn
  have hl : ∃lam : ℝ,0 < lam ∧ ∀ z∈S,lam ≤ gramQuadratic R z.1 z.2 := by
    by_cases hne : S.Nonempty
    · obtain ⟨z,hz,hm⟩ := hS.exists_isMinOn hne hcont
      exact ⟨_,hp z hz,fun w hw=>@hm w hw⟩
    · exact ⟨1,by norm_num,fun z hz=>(hne ⟨z,hz⟩).elim⟩
  obtain ⟨lam,hlam,hbound⟩ := hl
  refine ⟨lam,hlam,?_⟩
  intro θ hθ a
  by_cases ha : a=0
  · simp [ha,gramQuadratic]
  · have hn : ‖a‖≠0 := norm_ne_zero_iff.mpr ha
    have hunit : ‖‖a‖⁻¹ • a‖=1 := by simp [norm_smul,hn]
    have hh := hbound (θ,‖a‖⁻¹ • a) ⟨hθ,by simpa only [Metric.mem_sphere,dist_zero_right] using hunit⟩
    change lam ≤ gramQuadratic R θ (‖a‖⁻¹ • a) at hh
    rw [gramQuadratic_smul] at hh
    have h := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖a‖)
    have he : ((‖a‖⁻¹)^2*gramQuadratic R θ a)*‖a‖^2=gramQuadratic R θ a := by
      field_simp
    rwa [he] at h

theorem dotProduct_bound (a b : Parameter) : |a ⬝ᵥ b| ≤ 5*‖a‖*‖b‖ := by
  calc
    _ ≤ ∑ i : Fin 5,|a i*b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5,‖a‖*‖b‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

end
end Resonance.ActualGramCoercivity
