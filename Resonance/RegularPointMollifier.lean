import Resonance.CoordinatePermutation

/-! Every regular point of an actual C1 Euclidean level function has a genuine
localized delta limit. Nonzero gradient coordinates are chosen, not assumed
to be the middle coordinate. -/
open Set MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
namespace Resonance.RegularPointMollifier
noncomputable section
open LinearSurfaceArea CoordinateReplacement CoordinateLevelCoarea
open RegularGraphCoarea CoordinatePermutation CoareaIsometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem every_regular_point {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀p,HasFDerivAt F (innerSL ℝ (g p)) p) (hFC : ContDiff ℝ 1 F)
    (hg : Measurable g) (hc : 0<c) (p : A) (hn : g p≠0) :
    ∃ S : Set A, IsOpen S ∧ p∈S ∧
      ∀ (B : A → E), Continuous B → HasCompactSupport B → tsupport B⊆S →
      ∀ (ρ : ℝ → ℝ → ℝ),
      (∀η,0<η→Integrable (ρ η)) → (∀η,0<η→∀x,0≤ρ η x) →
      (∀η,0<η→∫x,ρ η x=1) → (∀η,0<η→∀x,ρ η x≠0→|x|≤η) →
      (∀η,0<η→IntegrableOn (fun z=>ρ η (F z) • B z) S) ∧
      IntegrableOn B (S∩{z|F z=0}) (regularMeasure F g c) ∧
      Tendsto (fun η=>c⁻¹ • ∫z in S,ρ η (F z) • B z)
        (𝓝[>]0) (𝓝 (∫z in S∩{z|F z=0},B z ∂regularMeasure F g c)) := by
  classical
  have hi : ∃i:Fin 3,g p i≠0 := by
    by_contra! hh
    apply hn
    ext i
    exact hh i
  obtain ⟨i,hi⟩ := hi
  let r := swapMiddle i
  let Ft := F ∘ r
  let gt := fun q=>r.symm (g (r q))
  have hFt : ContDiff ℝ 1 Ft := hFC.comp r.toContinuousLinearEquiv.contDiff
  have hgrad : ∀q,HasFDerivAt Ft (innerSL ℝ (gt q)) q := gradient_pullback hF r
  have hgm : Measurable gt := r.symm.continuous.measurable.comp (hg.comp r.continuous.measurable)
  have hpartial : (fderiv ℝ Ft (r.symm p)) (CoordinateReplacement.unit 1)≠0 := by
    rw [gradient_partial hgrad]
    simpa only [gt,r,swapMiddle_gradient] using hi
  obtain ⟨e,a,δ,he,ha,hδ,hsource,hFS,hinv,hjac⟩ :=
    ControlledCoordinateChart.exists_chart hFt.contDiffAt 1 hpartial
  have hpart : ∀q∈e.source,(fderiv ℝ Ft q) (CoordinateReplacement.unit 1)≠0 :=
    fun q hq=>abs_pos.mp (hδ.trans_le (hjac q hq))
  have hp : r.symm p∈e.source := by rw [hsource]; exact Metric.mem_ball_self ha
  refine ⟨r '' e.source,r.toHomeomorph.isOpenMap _ e.open_source,
    ⟨r.symm p,hp,r.apply_symm_apply p⟩,?_⟩
  intro B hB hK hS ρ hρ hpos hmass hsupp
  have hb := hB.comp r.continuous
  have hk := compact_pullback r hK
  have hs := pullback_support_source r hS
  have h := RegularNormalizedLimit.chart_limit hgrad hgm hc e he hFS hinv hpart
    hb hk hs ρ hρ hpos hmass hsupp
  have hr := preserving_regular_coarea r F hg c
  have hemb := r.toMeasurableEquiv.measurableEmbedding
  refine ⟨?_,?_,?_⟩
  · intro η hη
    exact (r.measurePreserving.integrableOn_image hemb).mpr (h.1 η hη)
  · rw [←image_inter_level r F e.source]
    exact (hr.integrableOn_image hemb).mpr h.2.1
  · rw [←image_inter_level r F e.source,hr.setIntegral_image_emb hemb B]
    simp_rw [r.measurePreserving.setIntegral_image_emb hemb]
    exact h.2.2

end
end Resonance.RegularPointMollifier
