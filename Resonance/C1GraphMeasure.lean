import Resonance.C1GraphArea
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! The actual graph area identity as a pushforward measure and as a weighted
nonnegative integral. These identities do not discard nonintegrable test functions. -/
open Set MeasureTheory
open scoped ENNReal EuclideanGeometry
namespace Resonance.C1GraphMeasure
noncomputable section
open LinearSurfaceArea C1GraphArea

theorem map_graph_area {H:P→ℝ} (hm:Measurable H) {T:Set P}
    (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T) :
    ((volume.restrict T).withDensity (fun x=>ENNReal.ofReal (jacobian H x))).map (graph H)=
      (μHE[2]:Measure A).restrict (graph H '' T) := by
  have hg:=graph_measurable hm
  apply Measure.ext
  intro s hs
  have hp:MeasurableSet (graph H ⁻¹' s):=hg hs
  have ht:MeasurableSet (graph H ⁻¹' s∩T):=hp.inter hT.measurableSet
  have hi:graph H '' (graph H ⁻¹' s∩T)=s∩graph H '' T:=by
    ext z
    constructor
    · rintro ⟨x,⟨hxs,hxT⟩,rfl⟩
      exact ⟨hxs,⟨x,hxT,rfl⟩⟩
    · rintro ⟨hzs,x,hxT,rfl⟩
      exact ⟨x,⟨hzs,hxT⟩,rfl⟩
  rw [Measure.map_apply hg hs,withDensity_apply _ hp,Measure.restrict_restrict hp,
    Measure.restrict_apply hs,←hi]
  exact (graph_image_area hT hH ht inter_subset_right).symm

theorem lintegral_graph_area {H:P→ℝ} (hm:Measurable H) {T:Set P}
    (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T) {B:A→ℝ≥0∞} (hB:Measurable B) :
    (∫⁻z in graph H '' T,B z ∂(μHE[2]:Measure A))=
      ∫⁻x in T,ENNReal.ofReal (jacobian H x)*B (graph H x) := by
  rw [←map_graph_area hm hT hH,lintegral_map hB (graph_measurable hm)]
  simpa only [Pi.mul_apply,Function.comp_apply] using
    lintegral_withDensity_eq_lintegral_mul (volume.restrict T) (jacobian_measurable H).ennreal_ofReal
      (hB.comp (graph_measurable hm))

theorem weighted_graph_area {H:P→ℝ} (hm:Measurable H) {T:Set P}
    (hT:IsOpen T) (hH:ContDiffOn ℝ 1 H T)
    {w B:A→ℝ≥0∞} (hw:Measurable w) (hB:Measurable B) :
    (∫⁻z,B z ∂((μHE[2]:Measure A).restrict (graph H '' T)).withDensity w)=
      ∫⁻x in T,ENNReal.ofReal (jacobian H x)*w (graph H x)*B (graph H x) := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hB]
  have h:=lintegral_graph_area hm hT hH (hw.mul hB)
  simp only [Pi.mul_apply] at h ⊢
  rw [h]
  apply lintegral_congr
  intro x
  exact (mul_assoc _ _ _).symm

end
end Resonance.C1GraphMeasure
