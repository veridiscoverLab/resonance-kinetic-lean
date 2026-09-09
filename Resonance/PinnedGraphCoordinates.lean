import Resonance.PinnedGraphCoarea
import Mathlib.MeasureTheory.Constructions.Pi

/-! The original (x,z) Lebesgue coordinates of the pinned resonance chart.
The planar Euclidean measure is explicitly identified with product Lebesgue
measure, not with the Hausdorff measure of the product sup metric. -/
open Set MeasureTheory
open scoped ENNReal Topology EuclideanGeometry
namespace Resonance.PinnedGraphCoordinates
noncomputable section
open LinearSurfaceArea PinnedMeasure PinnedMeasureNormalization

def pairEquiv : P≃L[ℝ](ℝ×ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 2=>ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

theorem pairEquiv_apply (x:P) : pairEquiv x=(x 0,x 1) := rfl

theorem pairEquiv_preserving : MeasurePreserving pairEquiv
    (volume:Measure P) (volume:Measure (ℝ×ℝ)) :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem original_graph_coarea_integral {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {H:ℝ×ℝ→ℝ} {S:Set (ℝ×ℝ)} (hS:IsOpen S) (hH:ContDiffOn ℝ 1 H S)
    (hE:∀p∈S,PinnedGeometry.energyDefect d p.1 (H p) p.2=0)
    (hy:∀p∈S,PinnedGeometry.velocity d (H p)≠PinnedGeometry.velocity d (p.1+H p-p.2))
    {B:Ambient→ℝ≥0∞} (hB:Measurable B) :
    (∫⁻k in graph H '' S,B k ∂euclideanLiftedRegularCoarea d)=
      ∫⁻p in S,ENNReal.ofReal (((2*Real.pi)^3*
        |PinnedGeometry.velocity d (H p)-PinnedGeometry.velocity d (p.1+H p-p.2)|)⁻¹)*B (graph H p) := by
  let T:=pairEquiv ⁻¹' S
  let H0:P→ℝ:=H∘pairEquiv
  have hT:IsOpen T:=hS.preimage pairEquiv.continuous
  have hH0:ContDiffOn ℝ 1 H0 T:=hH.comp pairEquiv.contDiff.contDiffOn (fun _ hx=>hx)
  have hg:∀x:P,C1GraphArea.graph H0 x=graph H (pairEquiv x):=fun _=>rfl
  have hE0:∀x∈T,liftedEnergy d (C1GraphArea.graph H0 x)=0:=by
    intro x hx
    exact hE (pairEquiv x) hx
  have hy0:∀x∈T,energyGradient d (C1GraphArea.graph H0 x) 1≠0:=by
    intro x hx
    exact sub_ne_zero.mpr (hy (pairEquiv x) hx)
  have h:=PinnedGraphCoarea.graph_coarea_integral hd0 hdU hT hH0 hE0 hy0 hB
  have himage:C1GraphArea.graph H0 '' T=graph H '' S:=by
    rw [show C1GraphArea.graph H0=graph H∘pairEquiv from funext hg,image_comp]
    congr 1
    exact Set.image_preimage_eq S pairEquiv.surjective
  rw [himage] at h
  rw [h]
  exact pairEquiv_preserving.setLIntegral_comp_preimage_emb
    (pairEquiv.continuous.measurableEmbedding pairEquiv.injective)
    (fun p=>ENNReal.ofReal (((2*Real.pi)^3*
      |PinnedGeometry.velocity d (H p)-PinnedGeometry.velocity d (p.1+H p-p.2)|)⁻¹)*B (graph H p)) S

end
end Resonance.PinnedGraphCoordinates
