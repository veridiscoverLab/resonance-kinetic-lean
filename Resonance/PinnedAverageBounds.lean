import Resonance.PinnedLocalSmooth

/-! Uniform bounds for the genuine source averages and their first target
derivative.  Derivatives are obtained by the already proved integration by
parts on the same graph; no derivative bound for the input function occurs. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedAverageBounds
noncomputable section
open Resonance.PinnedSmoothing Resonance.PinnedAveraging

theorem actual_L1_average_uniform_C1
    {I I₀ J K : Set ℝ}
    (hI : IsOpen I) (hI₀ : IsOpen I₀) (hJ : IsOpen J)
    (hK : IsCompact K) (hIK : I ⊆ K) (hKI : K ⊆ I₀)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ J)
    {H χ : ℝ × ℝ → ℝ}
    (hH : ContDiffOn ℝ ∞ H (I₀ ×ˢ J))
    (hχ : ContDiffOn ℝ ∞ χ (I₀ ×ˢ J))
    (hZ : ∀ p ∈ I₀ ×ˢ J, partialZ H p ≠ 0)
    (hχedge : ∀ x∈I₀, χ (x,a)=0 ∧ χ (x,b)=0)
    {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmap : ∀ x∈I, AEMeasurable (fun z => H (x,z)) (volume.restrict (Icc a b)))
    (hdom : ∀ x∈I, (volume.restrict (Icc a b)).map (fun z => H (x,z)) ≤ C • ν) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀ ≠ ⊤ ∧ C₁ ≠ ⊤ ∧
      ∀ f : ℝ→ℂ, Integrable f ν → ∀ x∈I,
        HasDerivAt (fun y => ∫ z in Icc a b, χ (y,z) • f (H (y,z)))
          (∫ z in Icc a b, transferWeight H χ (x,z) • f (H (x,z))) x ∧
        ‖∫ z in Icc a b, χ (x,z) • f (H (x,z))‖ₑ ≤ C₀*eLpNorm f 1 ν ∧
        ‖deriv (fun y => ∫ z in Icc a b, χ (y,z) • f (H (y,z))) x‖ₑ ≤
          C₁*eLpNorm f 1 ν := by
  let ψ := transferWeight H χ
  have hψ : ContDiffOn ℝ ∞ ψ (I₀×ˢJ) :=
    contDiffOn_transferWeight (hI₀.prod hJ) hH hχ hZ
  have hrect : K×ˢIcc a b ⊆ I₀×ˢJ := Set.prod_mono hKI hsub
  obtain ⟨B₀,hB₀⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hχ.continuousOn.mono hrect)
  obtain ⟨B₁,hB₁⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hψ.continuousOn.mono hrect)
  have hmeas {W : ℝ×ℝ→ℝ} (hW : ContinuousOn W (I₀×ˢJ)) (x : ℝ) (hx : x∈I) :
      AEStronglyMeasurable (fun z => W (x,z)) (volume.restrict (Icc a b)) :=
    (hW.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hKI (hIK hx),hsub hz⟩)).aestronglyMeasurable measurableSet_Icc
  have hb₀ : ∀ x∈I, ∀ᵐ z ∂volume.restrict (Icc a b), ‖χ (x,z)‖ ≤ B₀ := by
    intro x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact hB₀ (x,z) ⟨hIK hx,hz⟩
  have hb₁ : ∀ x∈I, ∀ᵐ z ∂volume.restrict (Icc a b), ‖ψ (x,z)‖ ≤ B₁ := by
    intro x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact hB₁ (x,z) ⟨hIK hx,hz⟩
  refine ⟨ENNReal.ofReal B₀*C, ENNReal.ofReal B₁*C,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC,?_⟩
  intro f hf x hx
  have hD : HasDerivAt (fun y => ∫ z in Icc a b, χ (y,z) • f (H (y,z)))
      (∫ z in Icc a b, ψ (x,z) • f (H (x,z))) x := by
    apply source_average_hasDerivAt_of_smooth_identity hI hC hmap hdom
      (hmeas hχ.continuousOn) (hmeas hψ.continuousOn) hb₀ hb₁ _ hf hx
    intro g _hgcompact hgsmooth y hy
    have hII : I×ˢJ ⊆ I₀×ˢJ := Set.prod_mono (hIK.trans hKI) (Subset.refl J)
    exact actual_smooth_average_derivative hI hJ hab hsub (hH.mono hII)
      (hχ.mono hII) (fun p hp => hZ p (hII hp))
      (fun t ht => hχedge t (hKI (hIK ht))) hgsmooth hy
  refine ⟨hD,?_,?_⟩
  · rw [eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_weighted_comp_le (hmap x hx) (hdom x hx) hC hf (hb₀ x hx)
  · rw [hD.deriv, eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_weighted_comp_le (hmap x hx) (hdom x hx) hC hf (hb₁ x hx)

end
end Resonance.PinnedAverageBounds
