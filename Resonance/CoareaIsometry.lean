import Resonance.RegularGraphBochner

/-! Exact covariance of the original Euclidean coarea under linear isometries.
This concerns Euclidean ambient area, not a product sup-metric surface measure. -/
open Set MeasureTheory
open scoped ENNReal EuclideanGeometry InnerProductSpace
namespace Resonance.CoareaIsometry
noncomputable section
open LinearSurfaceArea RegularGraphCoarea

theorem preserving_density {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {e : α → β} (he : MeasurePreserving e μ ν)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    MeasurePreserving e (μ.withDensity (w ∘ e)) (ν.withDensity w) := by
  refine ⟨he.measurable,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply he.measurable hs,withDensity_apply _ (he.measurable hs),
    withDensity_apply _ hs]
  exact he.setLIntegral_comp_preimage hs hw

theorem preserving_euclidean_area (e : A ≃ₗᵢ[ℝ] A) :
    MeasurePreserving e (μHE[2]:Measure A) (μHE[2]:Measure A) := by
  rw [PinnedMeasureNormalization.euclideanArea_eq_smul]
  exact (e.toIsometryEquiv.measurePreserving_hausdorffMeasure 2).smul_measure _

theorem gradient_pullback {F : A → ℝ} {g : A → A}
    (hF : ∀p,HasFDerivAt F (innerSL ℝ (g p)) p) (e : A ≃ₗᵢ[ℝ] A) (p : A) :
    HasFDerivAt (F ∘ e) (innerSL ℝ (e.symm (g (e p)))) p := by
  have h := (hF (e p)).comp p e.toContinuousLinearEquiv.hasFDerivAt
  convert h using 1
  ext v
  change inner ℝ (e.symm (g (e p))) v=inner ℝ (g (e p)) (e v)
  rw [←e.inner_map_map (e.symm (g (e p))) v,e.apply_symm_apply]

theorem preserving_regular_coarea (e : A ≃ₗᵢ[ℝ] A) (F : A → ℝ)
    {g : A → A} (hg : Measurable g) (c : ℝ) :
    MeasurePreserving e (regularMeasure (F ∘ e) (fun p=>e.symm (g (e p))) c)
      (regularMeasure F g c) := by
  have hw : Measurable (fun p=>ENNReal.ofReal ((c*‖g p‖)⁻¹)) := by fun_prop
  have he := (preserving_euclidean_area e).restrict_preimage_emb
    e.toMeasurableEquiv.measurableEmbedding {p|F p=0 ∧ g p≠0}
  have h := preserving_density he hw
  simpa [regularMeasure] using h

end
end Resonance.CoareaIsometry
