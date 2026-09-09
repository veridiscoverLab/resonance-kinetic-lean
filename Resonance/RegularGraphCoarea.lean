import Resonance.PinnedGraphCoarea

/-! Exact Euclidean graph coarea for an actual differentiable level function.
This permits coordinate permutations and nonzero nearby energy levels without
postulating a new surface measure or its density. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace EuclideanGeometry
namespace Resonance.RegularGraphCoarea
noncomputable section
open LinearSurfaceArea C1GraphArea C1GraphMeasure

def regularMeasure (F : A → ℝ) (g : A → A) (c : ℝ) : Measure A :=
  ((μHE[2] : Measure A).restrict {z | F z=0 ∧ g z≠0}).withDensity
    (fun z => ENNReal.ofReal ((c*‖g z‖)⁻¹))

theorem gradient_graph_orthogonal {F : A → ℝ} {g : A → A}
    (hF : ∀z, HasFDerivAt F (innerSL ℝ (g z)) z)
    {H : P → ℝ} {T : Set P} (hT : IsOpen T) (hH : ContDiffOn ℝ 1 H T)
    (hzero : ∀x∈T, F (graph H x)=0) {x : P} (hx : x∈T) (v : P) :
    inner ℝ (g (graph H x)) (graphLinear (fderiv ℝ H x) v)=0 := by
  have hdH : HasStrictFDerivAt H (fderiv ℝ H x) x :=
    (hH x hx |>.contDiffAt (hT.mem_nhds hx)).hasStrictFDerivAt (by norm_num)
  have hc := (hF (graph H x)).comp x (graph_hasStrictFDerivAt hdH).hasFDerivAt
  have hevent : (fun _ : P => (0:ℝ)) =ᶠ[𝓝 x] (fun y => F (graph H y)) := by
    filter_upwards [hT.mem_nhds hx] with y hy
    exact (hzero y hy).symm
  have hz : HasFDerivAt (fun y => F (graph H y)) (0:P→L[ℝ]ℝ) x :=
    (hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) x).congr_of_eventuallyEq hevent.symm
  exact congrArg (fun L : P→L[ℝ]ℝ => L v) (hc.unique hz)

theorem gradient_graph_norm {F : A → ℝ} {g : A → A}
    (hF : ∀z, HasFDerivAt F (innerSL ℝ (g z)) z)
    {H : P → ℝ} {T : Set P} (hT : IsOpen T) (hH : ContDiffOn ℝ 1 H T)
    (hzero : ∀x∈T, F (graph H x)=0) {x : P} (hx : x∈T) :
    ‖g (graph H x)‖ = |g (graph H x) 1| * jacobian H x :=
  PinnedGraphCoarea.graph_normal_norm _ _ (gradient_graph_orthogonal hF hT hH hzero hx)

theorem graph_integral_of_measurable {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z, HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : c≠0)
    {H : P → ℝ} (hm : Measurable H) {T : Set P} (hT : IsOpen T)
    (hH : ContDiffOn ℝ 1 H T) (hzero : ∀x∈T, F (graph H x)=0)
    (hy : ∀x∈T, g (graph H x) 1≠0) {B : A → ℝ≥0∞} (hB : Measurable B) :
    (∫⁻z in graph H '' T, B z ∂regularMeasure F g c) =
      ∫⁻x in T, ENNReal.ofReal ((c*|g (graph H x) 1|)⁻¹) * B (graph H x) := by
  have hgraph : MeasurableEmbedding (graph H) :=
    (graph_measurable hm).measurableEmbedding (graph_injective H)
  have him : MeasurableSet (graph H '' T) := hgraph.measurableSet_image.mpr hT.measurableSet
  have hsub : graph H '' T⊆{z | F z=0 ∧ g z≠0} := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hzero x hx,?_⟩
    intro he
    exact hy x hx (congrArg (fun z : A => z 1) he)
  have hmeq : (regularMeasure F g c).restrict (graph H '' T) =
      ((μHE[2] : Measure A).restrict (graph H '' T)).withDensity
        (fun z => ENNReal.ofReal ((c*‖g z‖)⁻¹)) := by
    unfold regularMeasure
    rw [restrict_withDensity him, Measure.restrict_restrict him, inter_eq_left.mpr hsub]
  have hw : Measurable (fun z => ENNReal.ofReal ((c*‖g z‖)⁻¹)) := by fun_prop
  rw [hmeq, weighted_graph_area hm hT hH hw hB]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hT.measurableSet] with x hx
  congr 1
  rw [gradient_graph_norm hF hT hH hzero hx,
    ←ENNReal.ofReal_mul (jacobian_pos H x).le]
  congr 1
  have hJ : jacobian H x≠0 := ne_of_gt (jacobian_pos H x)
  have ha : |g (graph H x) 1|≠0 := abs_ne_zero.mpr (hy x hx)
  field_simp

theorem graph_integral {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀z, HasFDerivAt F (innerSL ℝ (g z)) z) (hg : Measurable g) (hc : c≠0)
    {H : P → ℝ} {T : Set P} (hT : IsOpen T) (hH : ContDiffOn ℝ 1 H T)
    (hzero : ∀x∈T, F (graph H x)=0) (hy : ∀x∈T, g (graph H x) 1≠0)
    {B : A → ℝ≥0∞} (hB : Measurable B) :
    (∫⁻z in graph H '' T, B z ∂regularMeasure F g c) =
      ∫⁻x in T, ENNReal.ofReal ((c*|g (graph H x) 1|)⁻¹) * B (graph H x) := by
  classical
  let H0 := T.piecewise H (fun _ => 0)
  have hm : Measurable H0 := hH.continuousOn.measurable_piecewise continuousOn_const hT.measurableSet
  have heq : ∀x∈T, H x=H0 x := fun x hx => (Set.piecewise_eq_of_mem T H (fun _ => 0) hx).symm
  have hH0 : ContDiffOn ℝ 1 H0 T := hH.congr (fun x hx => (heq x hx).symm)
  have hgraph : ∀x∈T, graph H0 x=graph H x := by intro x hx; simp only [graph, ←heq x hx]
  have hz : ∀x∈T, F (graph H0 x)=0 := by intro x hx; rw [hgraph x hx]; exact hzero x hx
  have hy0 : ∀x∈T, g (graph H0 x) 1≠0 := by intro x hx; rw [hgraph x hx]; exact hy x hx
  have h := graph_integral_of_measurable hF hg hc hm hT hH0 hz hy0 hB
  rw [Set.image_congr hgraph] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hT.measurableSet] with x hx
  rw [hgraph x hx]

end
end Resonance.RegularGraphCoarea
