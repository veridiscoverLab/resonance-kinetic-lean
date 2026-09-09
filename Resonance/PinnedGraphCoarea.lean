import Resonance.C1GraphMeasure
import Resonance.PinnedMeasureNormalization

/-! Exact regular graph coarea for the original pinned dispersion. The surface
measure is the normalized Euclidean Hausdorff measure already used by the paper. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace EuclideanGeometry
namespace Resonance.PinnedGraphCoarea
noncomputable section
open LinearSurfaceArea C1GraphArea C1GraphMeasure PinnedMeasure PinnedMeasureNormalization

theorem graph_normal_norm (g:A) (l:P→L[ℝ]ℝ)
    (ho:∀v,inner ℝ g (graphLinear l v)=0) :
    ‖g‖=|g 1| * Real.sqrt (1+(l (e 0))^2+(l (e 1))^2) := by
  have h0:=ho (e 0)
  have h1:=ho (e 1)
  simp [graphLinear,PiLp.inner_apply,Fin.sum_univ_three,PlaneCoarea.real_inner_apply,e] at h0 h1
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity),sq_abs,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  have he0:g 0= -g 1*l (e 0):=by simpa only [e] using (show g 0= -g 1*l (EuclideanSpace.single 0 1) by nlinarith [h0])
  have he2:g 2= -g 1*l (e 1):=by simpa only [e] using (show g 2= -g 1*l (EuclideanSpace.single 1 1) by nlinarith [h1])
  rw [he0,he2]
  ring

theorem energyGradient_graph_orthogonal {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {H:P→ℝ} {T:Set P} (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T)
    (hE:∀x∈T,liftedEnergy d (C1GraphArea.graph H x)=0) {x:P} (hx:x∈T) (v:P) :
    inner ℝ (energyGradient d (C1GraphArea.graph H x)) (graphLinear (fderiv ℝ H x) v)=0 := by
  have hdH:HasStrictFDerivAt H (fderiv ℝ H x) x:=
    (hH x hx |>.contDiffAt (hT.mem_nhds hx)).hasStrictFDerivAt (by norm_num)
  have hc:HasFDerivAt (fun y=>liftedEnergy d (C1GraphArea.graph H y))
      ((innerSL ℝ (energyGradient d (C1GraphArea.graph H x))).comp (graphLinear (fderiv ℝ H x))) x:=
    (liftedEnergy_hasFDerivAt hd0 hdU _).comp x (graph_hasStrictFDerivAt hdH).hasFDerivAt
  have hevent:(fun _ : P=>(0:ℝ))=ᶠ[𝓝 x](fun y=>liftedEnergy d (C1GraphArea.graph H y)):=by
    filter_upwards [hT.mem_nhds hx] with y hy
    exact (hE y hy).symm
  have hz:HasFDerivAt (fun y=>liftedEnergy d (C1GraphArea.graph H y)) (0:P→L[ℝ]ℝ) x:=
    (hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) x).congr_of_eventuallyEq hevent.symm
  have he:=hc.unique hz
  have hv:=congrArg (fun L:P→L[ℝ]ℝ=>L v) he
  exact hv

theorem energyGradient_graph_norm {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {H:P→ℝ} {T:Set P} (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T)
    (hE:∀x∈T,liftedEnergy d (C1GraphArea.graph H x)=0) {x:P} (hx:x∈T) :
    ‖energyGradient d (C1GraphArea.graph H x)‖=
      |energyGradient d (C1GraphArea.graph H x) 1| * jacobian H x :=
  graph_normal_norm _ _ (energyGradient_graph_orthogonal hd0 hdU hT hH hE hx)

theorem coarea_graph_density {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {H:P→ℝ} {T:Set P} (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T)
    (hE:∀x∈T,liftedEnergy d (C1GraphArea.graph H x)=0)
    {x:P} (hx:x∈T) (hy:energyGradient d (C1GraphArea.graph H x) 1≠0) :
    ENNReal.ofReal (jacobian H x)*coareaWeight d (C1GraphArea.graph H x)=
      ENNReal.ofReal (((2*Real.pi)^3*|energyGradient d (C1GraphArea.graph H x) 1|)⁻¹) := by
  unfold coareaWeight
  rw [energyGradient_graph_norm hd0 hdU hT hH hE hx,
    ←ENNReal.ofReal_mul (jacobian_pos H x).le]
  congr 1
  have hJ:jacobian H x≠0:=ne_of_gt (jacobian_pos H x)
  have hpi:(2*Real.pi)^3≠0:=by positivity
  have habs:|energyGradient d (C1GraphArea.graph H x) 1|≠0:=abs_ne_zero.mpr hy
  field_simp

theorem graph_coarea_integral_of_measurable {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {H:P→ℝ} (hm:Measurable H) {T:Set P} (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T)
    (hE:∀x∈T,liftedEnergy d (C1GraphArea.graph H x)=0)
    (hy:∀x∈T,energyGradient d (C1GraphArea.graph H x) 1≠0)
    {B:A→ℝ≥0∞} (hB:Measurable B) :
    (∫⁻z in C1GraphArea.graph H '' T,B z ∂euclideanLiftedRegularCoarea d)=
      ∫⁻x in T,ENNReal.ofReal (((2*Real.pi)^3*
        |energyGradient d (C1GraphArea.graph H x) 1|)⁻¹)*B (C1GraphArea.graph H x) := by
  have hg:MeasurableEmbedding (C1GraphArea.graph H):=
    (graph_measurable hm).measurableEmbedding (graph_injective H)
  have himage:MeasurableSet (C1GraphArea.graph H '' T):=
    hg.measurableSet_image.mpr hT.measurableSet
  have hsub:C1GraphArea.graph H '' T⊆regularSurface d:=by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hE x hx,?_⟩
    intro hz
    exact hy x hx (congrArg (fun v:A=>v 1) hz)
  have hmueq:(euclideanLiftedRegularCoarea d).restrict (C1GraphArea.graph H '' T)=
      ((μHE[2]:Measure A).restrict (C1GraphArea.graph H '' T)).withDensity (coareaWeight d):=by
    unfold euclideanLiftedRegularCoarea
    rw [restrict_withDensity himage,Measure.restrict_restrict himage,inter_eq_left.mpr hsub]
  rw [hmueq,weighted_graph_area hm hT hH (coareaWeight_measurable hd0 hdU) hB]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hT.measurableSet] with x hx
  rw [coarea_graph_density hd0 hdU hT hH hE hx (hy x hx)]

theorem graph_coarea_integral {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {H:P→ℝ} {T:Set P} (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T)
    (hE:∀x∈T,liftedEnergy d (C1GraphArea.graph H x)=0)
    (hy:∀x∈T,energyGradient d (C1GraphArea.graph H x) 1≠0)
    {B:A→ℝ≥0∞} (hB:Measurable B) :
    (∫⁻z in C1GraphArea.graph H '' T,B z ∂euclideanLiftedRegularCoarea d)=
      ∫⁻x in T,ENNReal.ofReal (((2*Real.pi)^3*
        |energyGradient d (C1GraphArea.graph H x) 1|)⁻¹)*B (C1GraphArea.graph H x) := by
  classical
  let H0:=T.piecewise H (fun _=>0)
  have hm:Measurable H0:=hH.continuousOn.measurable_piecewise continuousOn_const hT.measurableSet
  have heq:∀x∈T,H x=H0 x:=fun x hx=>(Set.piecewise_eq_of_mem T H (fun _=>0) hx).symm
  have hH0:ContDiffOn ℝ 1 H0 T:=hH.congr (fun x hx=>(heq x hx).symm)
  have hgraph:∀x∈T,C1GraphArea.graph H0 x=C1GraphArea.graph H x:=by
    intro x hx
    simp only [C1GraphArea.graph,←heq x hx]
  have hE0:∀x∈T,liftedEnergy d (C1GraphArea.graph H0 x)=0:=by
    intro x hx
    rw [hgraph x hx]
    exact hE x hx
  have hy0:∀x∈T,energyGradient d (C1GraphArea.graph H0 x) 1≠0:=by
    intro x hx
    rw [hgraph x hx]
    exact hy x hx
  have h:=graph_coarea_integral_of_measurable hd0 hdU hm hT hH0 hE0 hy0 hB
  have himage:C1GraphArea.graph H0 '' T=C1GraphArea.graph H '' T:=Set.image_congr hgraph
  rw [himage] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hT.measurableSet] with x hx
  rw [hgraph x hx]

end
end Resonance.PinnedGraphCoarea
