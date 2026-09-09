import Resonance.OnsagerDriveFamily
import Resonance.ActualOnsagerPositive

/-! Continuity of the original Onsager tensor follows from the constructed
physical cell and the original projected sources. -/
open MeasureTheory
open scoped ENNReal BigOperators
namespace Resonance.ActualOnsagerContinuity
noncomputable section
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open ActualOnsagerTensor ActualOnsagerPositive BoundedSourceMaps OnsagerDriveFamily
open StrongCellParameterContinuity PhysicalVariationalCell

theorem actual_source_identity {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    functional hR (driveTop hR hθ i)=source hR hθ i := by
  ext u
  rw [functional_apply]
  change (∫k,u k*driveTop hR hθ i k∂cubeVolume R)=
    ReferenceMomentFunctionals.moment hR (drive_memLp_top hR hθ i) u
  rw [ReferenceMomentFunctionals.moment_apply]
  apply integral_congr_ae
  filter_upwards [driveTop_ae hR hθ i] with k hk
  rw [hk]

theorem actual_cell_identity {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    StrongBoundedCell.cell hR hθ (driveTop hR hθ i)=(transportCell hR hθ i : Space R) := by
  rw [StrongBoundedCell.cell_eq_weak hR hθ _ (driveTop_micro hR hθ i)]
  change (solve hR hθ (functional hR (driveTop hR hθ i)) : Space R)=_
  rw [actual_source_identity]
  rfl

theorem actual_source_continuous {R : ℝ} (hR : 0<R) (i : Index) :
    Continuous (fun θ : positiveDomain R=>source hR θ.property i) := by
  have hh := (functionalMap hR).continuous.comp (driveTop_continuous hR i)
  change Continuous (fun θ : positiveDomain R=>functional hR (driveTop hR θ.property i)) at hh
  simpa only [actual_source_identity] using hh

theorem actual_transportCell_continuous {R : ℝ} (hR : 0<R) (i : Index) :
    Continuous (fun θ : positiveDomain R=>(transportCell hR θ.property i : Space R)) := by
  have hh := (actual_cell_continuous hR).clm_apply (driveTop_continuous hR i)
  simpa only [actual_cell_identity] using hh

theorem actual_tensor_entry_continuous {R : ℝ} (hR : 0<R) (i j : Index) :
    Continuous (fun θ : positiveDomain R=>tensor hR θ.property i j) :=
  (actual_source_continuous hR i).clm_apply (actual_transportCell_continuous hR j)

theorem actual_tensor_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>tensor hR θ.property) :=
  continuous_pi (fun i=>continuous_pi (fun j=>actual_tensor_entry_continuous hR i j))

theorem actual_quadratic_joint_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun p : positiveDomain R×(Index→ℝ)=>quadraticResponse hR p.1.property p.2) := by
  unfold quadraticResponse
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  exact (((continuous_apply i).comp continuous_snd).mul
    ((actual_tensor_entry_continuous hR i j).comp continuous_fst)).mul
      ((continuous_apply j).comp continuous_snd)

end
end Resonance.ActualOnsagerContinuity
