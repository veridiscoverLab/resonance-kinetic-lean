import Resonance.PinnedOperator

/-! One original dispersion-dependent form bound for every positive
quartet weight with a common lower bound, retaining the maximal domain. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.PinnedUniformFormGap
noncomputable section
open PinnedMaximalDifference PinnedSmoothDomain PinnedClosedForm PinnedClassificationFinal

theorem uniform_form_lower_bound {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (a : FourCircle → ℝ), Continuous a →
      ∀ (b : ℝ), 0 < b → (∀ k, b ≤ a k) → ∀ (γ : ℝ), 0 ≤ γ →
      ∀ u : FormDomain hd0 hdU a,
        (γ/4)*(b*lam)*‖(u : Source)-(PinnedGap.nullSpace hd0 hdU a).starProjection u‖^2
          ≤ (form hd0 hdU a γ u u).re := by
  obtain ⟨lam,hlam,hgap⟩ := PinnedGap.uniform_lower_weight_spectral_gap hd0 hdU
  refine ⟨lam,hlam,fun a ha b hb hab γ hγ u => ?_⟩
  have hp : ∀ k, 0 < a k := fun k => lt_of_lt_of_le hb (hab k)
  have he := PinnedGap.nullSpace_weight_independent hd0 hdU a (fun _ => 1)
    ha hp continuous_const (fun _ => by norm_num)
  have hproj (f : Source) : (PinnedGap.nullSpace hd0 hdU (fun _ => 1)).starProjection f =
      (PinnedGap.nullSpace hd0 hdU a).starProjection f := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact he ▸ (PinnedGap.nullSpace hd0 hdU a).starProjection_apply_mem f
    · exact (congrArg Submodule.orthogonal he) ▸
        (PinnedGap.nullSpace hd0 hdU a).sub_starProjection_mem_orthogonal f
  have h := hgap a b hb hab (u : Source)
  rw [hproj,PinnedOperator.finite_energy_eq_ofReal_integral hd0 hdU a u] at h
  have hn : ENNReal.ofReal (b*lam)*‖(u : Source)-(PinnedGap.nullSpace hd0 hdU a).starProjection u‖ₑ^2 =
      ENNReal.ofReal ((b*lam)*‖(u : Source)-(PinnedGap.nullSpace hd0 hdU a).starProjection u‖^2) := by
    rw [ENNReal.ofReal_mul (mul_pos hb hlam).le,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  rw [hn] at h
  have hi0 : 0 ≤ ∫ k, ‖difference (u : Source) k‖^2 ∂weightedCoarea d a :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hr := (ENNReal.ofReal_le_ofReal_iff hi0).mp h
  rw [form_diagonal]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr (div_nonneg hγ (by norm_num))

end
end Resonance.PinnedUniformFormGap
