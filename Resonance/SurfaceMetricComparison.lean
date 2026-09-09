import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Quantitative comparison of the actual normalized Hausdorff area of two
parameterized surfaces. This is a local metric step towards an exact C¹ area
formula; no equality of surface measures is postulated. -/
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology EuclideanGeometry
namespace Resonance.SurfaceMetricComparison
noncomputable section

theorem normalized_area_lipschitzOn_le {E F:Type*} [MetricSpace E] [MetricSpace F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {f:E→F} {s:Set E} {K:ℝ≥0} (h:LipschitzOnWith K f s) (d:ℕ) :
    (μHE[d]:Measure F) (f '' s)≤(K:ℝ≥0∞)^d*(μHE[d]:Measure E) s := by
  have hb:=h.hausdorffMeasure_image_le (d:=(d:ℝ)) (by positivity)
  simp only [ENNReal.rpow_natCast] at hb
  simp only [Measure.euclideanHausdorffMeasure_def,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
  calc
    _ ≤ _ := mul_le_mul_right hb _
    _ = _ := by ac_rfl

theorem normalized_area_image_comparison {X E F:Type*} [Nonempty X]
    [MetricSpace E] [MetricSpace F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] (f:X→F) (g:X→E)
    (hg:Function.Injective g) (s:Set X) (K:ℝ≥0)
    (h:∀x∈s,∀y∈s,dist (f x) (f y)≤K*dist (g x) (g y)) (d:ℕ) :
    (μHE[d]:Measure F) (f '' s)≤(K:ℝ≥0∞)^d*(μHE[d]:Measure E) (g '' s) := by
  let e:E→F := fun p=>f (Function.invFun g p)
  have hi:=Function.leftInverse_invFun hg
  have hLip:LipschitzOnWith K e (g '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    simpa only [e,hi x,hi y] using h x hx y hy
  have he:e '' (g '' s)=f '' s := by
    rw [←image_comp]
    congr 1
    funext x
    exact congrArg f (hi x)
  simpa only [he] using normalized_area_lipschitzOn_le hLip d

theorem strict_derivative_metric_comparison {E F:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f:E→F} {L:E→L[ℝ]F} {x:E} (hf:HasStrictFDerivAt f L x)
    (hL:∀v,‖v‖≤‖L v‖) {ε:ℝ} (hε:0<ε) (hε1:ε<1) :
    ∃U:Set E,IsOpen U∧x∈U∧
      (∀y∈U,∀z∈U,dist (f y) (f z)≤(1+ε)*dist (L y) (L z))∧
      (∀y∈U,∀z∈U,dist (L y) (L z)≤(1-ε)⁻¹*dist (f y) (f z)) := by
  obtain ⟨U,hU,hx,hb⟩ := exists_nhds_square (hf.isLittleO.def hε)
  have herr:∀y∈U,∀z∈U,‖f y-f z-L (y-z)‖≤ε*‖L (y-z)‖ := by
    intro y hy z hz
    have hb' : ‖f y-f z-L (y-z)‖≤ε*‖y-z‖ := hb (show (y,z)∈U×ˢU from ⟨hy,hz⟩)
    exact hb'.trans (mul_le_mul_of_nonneg_left (hL (y-z)) hε.le)
  refine ⟨U,hU,hx,?_,?_⟩
  · intro y hy z hz
    have he:=herr y hy z hz
    have ht:=norm_add_le (f y-f z-L (y-z)) (L (y-z))
    rw [sub_add_cancel] at ht
    simp only [dist_eq_norm,←L.map_sub]
    nlinarith
  · intro y hy z hz
    have he:=herr y hy z hz
    have ht:=norm_sub_norm_le (L (y-z)) (f y-f z)
    rw [norm_sub_rev (L (y-z)) (f y-f z)] at ht
    simp only [dist_eq_norm,←L.map_sub]
    rw [mul_comm,←div_eq_mul_inv]
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    nlinarith

end
end Resonance.SurfaceMetricComparison
