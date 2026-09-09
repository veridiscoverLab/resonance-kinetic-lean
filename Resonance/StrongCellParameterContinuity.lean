import Resonance.CompactParameterCell
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-! Callable operator-norm continuous families on the entire original
positive domain, as opposed to merely separate existence at each parameter. -/
open Set
open scoped Topology ENNReal
namespace Resonance.StrongCellParameterContinuity
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure Thermodynamics ActualPairNormalization
open CompactParameterCell StrongBoundedCell LinftyFiveAugmentation LinftyPhysicalDomain

theorem continuous_of_compact_positive {R : ℝ} {B : Type*} [TopologicalSpace B]
    (f : positiveDomain R→B)
    (hf : ∀(K : Set Parameter)(_hK : IsCompact K)(hpos : K⊆positiveDomain R),
      Continuous (fun θ : K=>f ⟨θ,hpos θ.property⟩)) : Continuous f := by
  apply continuous_from_compactlyGeneratedSpace f
  intro T _ _ _ g hg
  let K : Set Parameter := Set.range (fun x : T=>(g x : Parameter))
  have hK : IsCompact K := isCompact_range (continuous_subtype_val.comp hg)
  have hpos : K⊆positiveDomain R := by
    rintro θ ⟨x,rfl⟩
    exact (g x).property
  let h : T→K := fun x=>⟨g x,⟨x,rfl⟩⟩
  have hc : Continuous h := (continuous_subtype_val.comp hg).subtype_mk _
  exact (hf K hK hpos).comp hc

def profileContinuous {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    C(cube R,ℝ) :=
  ⟨fun k=>WeightedJointMeasure.profile θ k,(FrequencyWeightedKernel.profile_continuousOn hθ).restrict⟩

theorem compact_profile_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>profileContinuous (hpos θ.property)) := by
  obtain ⟨m,M,C,hm,hM,hC,hb,hd⟩ := ProfileParameterBounds.compact_profile_lipschitz hR.le hK hpos
  apply subtype_continuous_of_bound hC
  intro θ β
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).mpr
  intro k
  exact hd θ θ.property β β.property k k.property

theorem actual_profile_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>profileContinuous θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_profile_continuous hR hK hpos)

theorem actual_analysis_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>PhysicalFiveBasis.analysisMap hR θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_analysis_continuous hR hK hpos)

theorem actual_synthesis_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>synthesisTop θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_synthesis_continuous hR hK hpos)

theorem actual_operator_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>AmbientLinftyCompact.operator hR θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_operator_continuous hR hK hpos)

theorem actual_divide_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>divide hR θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_divide_continuous hR hK hpos)

theorem actual_augmented_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>augmented hR θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_augmented_continuous hR hK hpos)

theorem actual_coordinate_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>coordinate hR θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_coordinate_continuous hR hK hpos)

theorem actual_cell_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>StrongBoundedCell.cell hR θ.property) :=
  continuous_of_compact_positive _ (fun _ hK hpos=>compact_cell_continuous hR hK hpos)

theorem actual_cell_joint_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun z : positiveDomain R×MeasureTheory.Lp ℝ ∞ (cubeVolume R)=>
      StrongBoundedCell.cell hR z.1.property z.2) :=
  ((actual_cell_continuous hR).comp continuous_fst).clm_apply continuous_snd

end
end Resonance.StrongCellParameterContinuity
