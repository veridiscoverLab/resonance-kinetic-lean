import Resonance.RegularGraphCoarea
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The exact graph coarea as a measure equality and a signed integral identity.
The density is finite, and integrability is retained as an explicit equivalence. -/
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace Resonance.RegularGraphBochner
noncomputable section
open LinearSurfaceArea C1GraphArea RegularGraphCoarea

theorem map_graph_coarea {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z,HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : c≠0)
    {H : P → ℝ} (hm : Measurable H) {T : Set P} (hT : IsOpen T)
    (hH : ContDiffOn ℝ 1 H T) (hz : ∀x∈T,F (graph H x)=0)
    (hy : ∀x∈T,g (graph H x) 1≠0) :
    ((volume.restrict T).withDensity
      (fun x=>ENNReal.ofReal ((c*|g (graph H x) 1|)⁻¹))).map (graph H)=
        (regularMeasure F g c).restrict (graph H '' T) := by
  have hmgraph := graph_measurable hm
  have hw : Measurable (fun x=>ENNReal.ofReal ((c*|g (graph H x) 1|)⁻¹)) := by fun_prop
  apply Measure.ext_of_lintegral
  intro B hB
  rw [lintegral_map hB hmgraph]
  change (∫⁻x,(B ∘ graph H) x ∂(volume.restrict T).withDensity
    (fun x=>ENNReal.ofReal ((c*|g (graph H x) 1|)⁻¹)))=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hw (hB.comp hmgraph)]
  exact (graph_integral_of_measurable hF hg hc hm hT hH hz hy hB).symm

theorem graph_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z,HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : 0<c)
    {H : P → ℝ} (hm : Measurable H) {T : Set P} (hT : IsOpen T)
    (hH : ContDiffOn ℝ 1 H T) (hz : ∀x∈T,F (graph H x)=0)
    (hy : ∀x∈T,g (graph H x) 1≠0) (B : A → E) :
    ∫z in graph H '' T,B z ∂regularMeasure F g c =
      ∫x in T,((c*|g (graph H x) 1|)⁻¹) • B (graph H x) := by
  have hmgraph : MeasurableEmbedding (graph H) :=
    (graph_measurable hm).measurableEmbedding (graph_injective H)
  have hmg := graph_measurable hm
  have hw : Measurable (fun x=>ENNReal.ofReal ((c*|g (graph H x) 1|)⁻¹)) := by fun_prop
  rw [←map_graph_coarea hF hg (ne_of_gt hc) hm hT hH hz hy,
    hmgraph.integral_map,
    integral_withDensity_eq_integral_toReal_smul hw (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hc.le (abs_nonneg _)))]

theorem graph_integrable_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z,HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : 0<c)
    {H : P → ℝ} (hm : Measurable H) {T : Set P} (hT : IsOpen T)
    (hH : ContDiffOn ℝ 1 H T) (hz : ∀x∈T,F (graph H x)=0)
    (hy : ∀x∈T,g (graph H x) 1≠0) (B : A → E) :
    IntegrableOn B (graph H '' T) (regularMeasure F g c) ↔
      IntegrableOn (fun x=>((c*|g (graph H x) 1|)⁻¹) • B (graph H x)) T := by
  have hmgraph : MeasurableEmbedding (graph H) :=
    (graph_measurable hm).measurableEmbedding (graph_injective H)
  have hmg := graph_measurable hm
  have hw : Measurable (fun x=>ENNReal.ofReal ((c*|g (graph H x) 1|)⁻¹)) := by fun_prop
  unfold IntegrableOn
  rw [←map_graph_coarea hF hg (ne_of_gt hc) hm hT hH hz hy,
    hmgraph.integrable_map_iff,
    integrable_withDensity_iff_integrable_smul' hw (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hc.le (abs_nonneg _))),Function.comp_apply]

theorem local_graph_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z,HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : 0<c)
    {H : P → ℝ} {T : Set P} (hT : IsOpen T)
    (hH : ContDiffOn ℝ 1 H T) (hz : ∀x∈T,F (graph H x)=0)
    (hy : ∀x∈T,g (graph H x) 1≠0) (B : A → E) :
    ∫z in graph H '' T,B z ∂regularMeasure F g c =
      ∫x in T,((c*|g (graph H x) 1|)⁻¹) • B (graph H x) := by
  classical
  let H0 := T.piecewise H (fun _=>0)
  have hm : Measurable H0 := hH.continuousOn.measurable_piecewise continuousOn_const hT.measurableSet
  have he : ∀x∈T,H0 x=H x := fun x hx=>Set.piecewise_eq_of_mem T H (fun _=>0) hx
  have hgph : ∀x∈T,graph H0 x=graph H x := by intro x hx; simp only [graph,he x hx]
  have hc0 : ContDiffOn ℝ 1 H0 T := hH.congr he
  have hz0 : ∀x∈T,F (graph H0 x)=0 := fun x hx=>hgph x hx ▸ hz x hx
  have hy0 : ∀x∈T,g (graph H0 x) 1≠0 := fun x hx=>hgph x hx ▸ hy x hx
  have hi := graph_integral hF hg hc hm hT hc0 hz0 hy0 B
  rw [Set.image_congr hgph] at hi
  rw [hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hT.measurableSet] with x hx
  rw [hgph x hx]

theorem local_graph_integrable_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z,HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : 0<c)
    {H : P → ℝ} {T : Set P} (hT : IsOpen T)
    (hH : ContDiffOn ℝ 1 H T) (hz : ∀x∈T,F (graph H x)=0)
    (hy : ∀x∈T,g (graph H x) 1≠0) (B : A → E) :
    IntegrableOn B (graph H '' T) (regularMeasure F g c) ↔
      IntegrableOn (fun x=>((c*|g (graph H x) 1|)⁻¹) • B (graph H x)) T := by
  classical
  let H0 := T.piecewise H (fun _=>0)
  have hm : Measurable H0 := hH.continuousOn.measurable_piecewise continuousOn_const hT.measurableSet
  have he : ∀x∈T,H0 x=H x := fun x hx=>Set.piecewise_eq_of_mem T H (fun _=>0) hx
  have hgph : ∀x∈T,graph H0 x=graph H x := by intro x hx; simp only [graph,he x hx]
  have hc0 : ContDiffOn ℝ 1 H0 T := hH.congr he
  have hz0 : ∀x∈T,F (graph H0 x)=0 := fun x hx=>hgph x hx ▸ hz x hx
  have hy0 : ∀x∈T,g (graph H0 x) 1≠0 := fun x hx=>hgph x hx ▸ hy x hx
  have hi := graph_integrable_iff hF hg hc hm hT hc0 hz0 hy0 B
  rw [Set.image_congr hgph] at hi
  refine hi.trans (integrable_congr ?_)
  filter_upwards [ae_restrict_mem hT.measurableSet] with x hx
  rw [hgph x hx]

end
end Resonance.RegularGraphBochner
