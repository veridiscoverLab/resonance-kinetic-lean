import Resonance.SurfaceAreaDensity
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! The exact Euclidean area formula for a real C¹ graph on an open planar
domain. The graph is not assumed globally C¹, and no surface formula is an input. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace EuclideanGeometry
namespace Resonance.C1GraphArea
noncomputable section
open LinearSurfaceArea SurfaceAreaDensity

def graph (H:P→ℝ) (x:P) : A := WithLp.toLp 2 ![x 0,H x,x 1]
def jacobian (H:P→ℝ) (x:P) : ℝ :=
  Real.sqrt (1+(fderiv ℝ H x (e 0))^2+(fderiv ℝ H x (e 1))^2)

theorem graph_injective (H:P→ℝ) : Function.Injective (graph H) := by
  intro x y h
  ext i
  fin_cases i
  · exact congrArg (fun z:A=>z 0) h
  · exact congrArg (fun z:A=>z 2) h

theorem graph_measurable {H:P→ℝ} (hH:Measurable H) : Measurable (graph H) := by
  unfold graph
  apply (PiLp.continuous_toLp 2 (fun _:Fin 3=>ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact (PiLp.continuous_apply 2 (fun _:Fin 2=>ℝ) 0).measurable
  · exact hH
  · exact (PiLp.continuous_apply 2 (fun _:Fin 2=>ℝ) 1).measurable

theorem graphLinear_expansive (l:P→L[ℝ]ℝ) (v:P) : ‖v‖≤‖graphLinear l v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,Fin.sum_univ_three]
  change (v 0)^2+(v 1)^2≤(v 0)^2+(l v)^2+(v 1)^2
  nlinarith [sq_nonneg (l v)]

theorem jacobian_pos (H:P→ℝ) (x:P) : 0<jacobian H x := by
  apply Real.sqrt_pos.mpr
  positivity

theorem jacobian_measurable (H:P→ℝ) : Measurable (jacobian H) := by
  have h0:=measurable_fderiv_apply_const ℝ H (e 0)
  have h1:=measurable_fderiv_apply_const ℝ H (e 1)
  exact Real.continuous_sqrt.measurable.comp ((measurable_const.add (h0.pow_const 2)).add (h1.pow_const 2))

theorem jacobian_continuousOn {H:P→ℝ} {T:Set P} (hT:IsOpen T)
    (hH:ContDiffOn ℝ 1 H T) : ContinuousOn (jacobian H) T := by
  have hd:=hH.continuousOn_fderiv_of_isOpen hT (by norm_num)
  have h0:=hd.clm_apply (g:=fun _=>e 0) continuousOn_const
  have h1:=hd.clm_apply (g:=fun _=>e 1) continuousOn_const
  exact Real.continuous_sqrt.comp_continuousOn ((continuousOn_const.add (h0.pow 2)).add (h1.pow 2))

theorem graph_hasStrictFDerivAt {H:P→ℝ} {x:P} {l:P→L[ℝ]ℝ}
    (hH:HasStrictFDerivAt H l x) : HasStrictFDerivAt (graph H) (graphLinear l) x := by
  rw [hasStrictFDerivAt_piLp]
  intro i
  fin_cases i
  · convert PiLp.hasStrictFDerivAt_apply (𝕜:=ℝ) 2 x (0:Fin 2) using 1
  · convert hH using 1
  · convert PiLp.hasStrictFDerivAt_apply (𝕜:=ℝ) 2 x (1:Fin 2) using 1

theorem graph_image_area {H:P→ℝ} {T:Set P} (hT:IsOpen T)
    (hH:ContDiffOn ℝ 1 H T) {s:Set P} (hs:MeasurableSet s) (hst:s⊆T) :
    (μHE[2]:Measure A) (graph H '' s)=∫⁻x in s,ENNReal.ofReal (jacobian H x) := by
  classical
  let H0:=T.piecewise H (fun _=>0)
  have hm:Measurable H0:=hH.continuousOn.measurable_piecewise continuousOn_const hT.measurableSet
  have hg:MeasurableEmbedding (graph H0):=(graph_measurable hm).measurableEmbedding (graph_injective H0)
  have heq:∀x∈T,H0 x=H x:=fun x hx=>Set.piecewise_eq_of_mem T H (fun _=>0) hx
  have hd:∀x∈T,HasStrictFDerivAt (graph H0) (graphLinear (fderiv ℝ H x)) x:=by
    intro x hx
    have hdf:HasStrictFDerivAt H (fderiv ℝ H x) x:=
      (hH x hx |>.contDiffAt (hT.mem_nhds hx)).hasStrictFDerivAt (by norm_num)
    have hevent:H=ᶠ[𝓝 x]H0:=by
      filter_upwards [hT.mem_nhds hx] with y hy
      exact (heq y hy).symm
    exact graph_hasStrictFDerivAt (hdf.congr_of_eventuallyEq hevent)
  have hare:=surfaceMeasure_eq_density_on (graph H0) hg T hT
    (fun x=>graphLinear (fderiv ℝ H x)) (jacobian H) (jacobian_measurable H)
    (jacobian_continuousOn hT hH) hd (fun x _=>graphLinear_expansive _)
    (fun x _=>(graphLinear_gram (fderiv ℝ H x)).symm) (fun x _=>jacobian_pos H x)
  have hset:=congrArg (fun μ:Measure P=>μ s) hare
  have him:graph H0 '' s=graph H '' s:=by
    apply Set.image_congr
    intro x hx
    simp only [graph,heq x (hst hx)]
  simpa only [surfaceMeasure,densityMeasure,Measure.restrict_apply hs,inter_eq_left.mpr hst,
    Measure.comap_apply _ hg.injective (fun t ht=>hg.measurableSet_image.mpr ht) _ hs,
    withDensity_apply _ hs,him] using hset

end
end Resonance.C1GraphArea
