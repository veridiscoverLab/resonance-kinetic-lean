import Resonance.PhysicalProjectionUniform
import Resonance.PhysicalFormUniformBounds

/-! The manuscript's unweighted microcondition controls the full original
weighted norm, uniformly on every compact positive RJ parameter family. -/
open Set
namespace Resonance.PhysicalMicroCoercivity
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalMomentProjection PhysicalProjectionKernel PhysicalProjectionUniform
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalFormUniformBounds

theorem micro_distance_bound {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E→L[ℝ]F) (P : E→L[ℝ]E) {C : ℝ}
    (hbound : ∀v,‖P v‖≤C*‖v‖) (hfix : ∀v∈T.ker,P v=v)
    {u : E} (hu : P u=0) : ‖u‖≤(1+C)*‖u-T.ker.starProjection u‖ := by
  let k := T.ker.starProjection u
  have hk : k∈T.ker := T.ker.starProjection_apply_mem u
  have he : u=(u-k)-P (u-k) := by
    rw [map_sub,hu,hfix k hk]
    module
  calc
    ‖u‖=‖(u-k)-P (u-k)‖ := congrArg norm he
    _ ≤ ‖u-k‖+‖P (u-k)‖ := norm_sub_le _ _
    _ ≤ ‖u-k‖+C*‖u-k‖ := add_le_add le_rfl (hbound _)
    _ = _ := by dsimp [k]; ring

theorem actual_microcoercivity {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃c C : ℝ,0 < c ∧ 0≤C ∧ ∀θ,(hθ : θ∈K) → ∀u : Space R,
      projection hR (hpos hθ) u=0 →
      c*‖u‖^2≤physicalForm hR.le (hpos hθ) u u ∧
      physicalForm hR.le (hpos hθ) u u≤C*‖u‖^2 := by
  obtain ⟨δ,hδ,hgap⟩ := physical_uniform_coercivity hR hK hpos
  obtain ⟨B,hB,hbound⟩ := projection_uniform_bound hR hK hpos
  obtain ⟨C,hC,hupper⟩ := physical_form_uniform_upper hR hK hpos
  have hb : 0<(1+B)^2 := sq_pos_of_pos (by linarith)
  refine ⟨δ/(1+B)^2,C,div_pos hδ hb,hC,?_⟩
  intro θ hθ u hu
  refine ⟨?_,hupper θ hθ u⟩
  have hd := micro_distance_bound (physicalDifference hR.le (hpos hθ))
    (projection hR (hpos hθ)) (hbound θ hθ)
    (fun v hv=>projection_fixed_kernel hR (hpos hθ) hv) hu
  have hs := mul_self_le_mul_self (norm_nonneg u) hd
  have hg := hgap θ hθ u
  rw [div_mul_eq_mul_div,div_le_iff₀ hb]
  nlinarith [mul_nonneg hδ.le (show 0≤
    ((1+B)*‖u-(physicalDifference hR.le (hpos hθ)).ker.starProjection u‖)^2-‖u‖^2 by
      nlinarith)]

end
end Resonance.PhysicalMicroCoercivity
