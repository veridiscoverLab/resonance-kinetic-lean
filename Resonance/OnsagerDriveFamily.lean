import Resonance.BoundedSourceMaps
import Resonance.StrongCellParameterContinuity
import Resonance.ActualOnsagerTensor
import Resonance.PhysicalProjectionUniform

/-! A continuous bounded family of the original projected fifteen drives.
The projection is identified through the same physical source embedding. -/
open MeasureTheory
open scoped ENNReal BigOperators
namespace Resonance.OnsagerDriveFamily
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open PhysicalFiveBasis PhysicalMomentProjection BoundedCellSource BoundedSourceMaps
open LinftyFiveAugmentation StrongCellParameterContinuity ActualOnsagerTensor
open CoareaNormalization (euclideanFive euclideanFive_continuous)

def driveWeight (R : ℝ) (i : Index) : C(cube R,ℝ) :=
  ⟨fun k=>(2*(k : E) i.1)*euclideanFive i.2 k,
    ((((PiLp.proj 2 (fun _ : Fin 3=>ℝ) i.1 : E→L[ℝ]ℝ).continuous.comp
      continuous_subtype_val).const_mul 2).mul
        ((euclideanFive_continuous i.2).comp continuous_subtype_val))⟩

def rawContinuous {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Index) :
    C(cube R,ℝ) := profileContinuous hθ*driveWeight R i

theorem rawContinuous_apply {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i : Index) (k : cube R) : rawContinuous hθ i k=rawDrive θ i k := by
  change WeightedJointMeasure.profile θ k*((2*(k : E) i.1)*euclideanFive i.2 k)=
    (2*(k : E) i.1)*(WeightedJointMeasure.profile θ k*euclideanFive i.2 k)
  ring

def rawTop {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Index) :
    Lp ℝ ∞ (cubeVolume R) := CubeLinftyCoordinates.embed R (rawContinuous hθ i)

theorem rawTop_ae {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Index) :
    rawTop hθ i=ᵐ[cubeVolume R]rawDrive θ i := by
  filter_upwards [CubeLinftyCoordinates.embed_ae R (rawContinuous hθ i),
    ae_restrict_mem (measurable_cube R)] with k he hk
  exact he.trans ((CubeLinftyCoordinates.zeroExtension_apply R
    (rawContinuous hθ i) ⟨k,hk⟩).trans (rawContinuous_apply hθ i ⟨k,hk⟩))

theorem rawTop_continuous {R : ℝ} (hR : 0<R) (i : Index) :
    Continuous (fun θ : positiveDomain R=>rawTop θ.property i) :=
  (CubeLinftyCoordinates.embed R).continuous.comp
    ((actual_profile_continuous hR).mul continuous_const)

theorem sourceMap_raw {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    sourceMap hR (rawTop hθ i)=boundedVector hR (rawDrive_memLp_top hθ i) := by
  apply Lp.ext
  apply (reference_volume_equivalent hR).2.ae_eq
  exact ((sourceVector_ae hR (rawTop hθ i)).trans (rawTop_ae hθ i)).trans
    (boundedVector_ae hR (rawDrive_memLp_top hθ i)).symm

theorem sourceMap_synthesis {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    sourceMap hR (synthesisTop hθ b)=synthesis hR.le hθ b := by
  apply Lp.ext
  apply (reference_volume_equivalent hR).2.ae_eq
  filter_upwards [sourceVector_ae hR (synthesisTop hθ b),synthesisTop_ae hθ b,
    (reference_volume_equivalent hR).1.ae_eq (synthesis_ae hR.le hθ b)] with k hs ht hb
  change StrongBoundedCell.sourceVector hR (synthesisTop hθ b) k=synthesis hR.le hθ b k
  rw [hs,ht,hb]
  simp only [basisFunction,Entropy.denominator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def driveTop {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i : Index) : Lp ℝ ∞ (cubeVolume R) := rawTop hθ i-
      synthesisTop hθ (gramInverse hR hθ (analysisMap hR hθ (sourceMap hR (rawTop hθ i))))

theorem sourceMap_drive {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    sourceMap hR (driveTop hR hθ i)=boundedVector hR (drive_memLp_top hR hθ i) := by
  rw [driveTop,map_sub,sourceMap_synthesis,sourceMap_raw]
  exact (BoundedMicroProjection.projectDrive_vector hR hθ (rawDrive_memLp_top hθ i)).symm

theorem driveTop_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    driveTop hR hθ i=ᵐ[cubeVolume R]drive hR hθ i := by
  have he : StrongBoundedCell.sourceVector hR (driveTop hR hθ i)=
      boundedVector hR (drive_memLp_top hR hθ i) := sourceMap_drive hR hθ i
  have hs := sourceVector_ae hR (driveTop hR hθ i)
  rw [he] at hs
  exact hs.symm.trans (boundedVector_ae hR (drive_memLp_top hR hθ i))

theorem driveTop_micro {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    projection hR hθ (StrongBoundedCell.sourceVector hR (driveTop hR hθ i))=0 := by
  change projection hR hθ (sourceMap hR (driveTop hR hθ i))=0
  rw [sourceMap_drive]
  exact drive_micro hR hθ i

theorem inverseGram_continuous {R : ℝ} (hR : 0<R) :
    Continuous (fun θ : positiveDomain R=>gramInverse hR θ.property) := by
  have hh := continuousOn_iff_continuous_restrict.mp
    (PhysicalProjectionUniform.inverseGramFunction_continuousOn hR)
  change Continuous (fun θ : positiveDomain R=>PhysicalProjectionUniform.inverseGramFunction R θ) at hh
  have he : (fun θ : positiveDomain R=>gramInverse hR θ.property)=
      (fun θ : positiveDomain R=>PhysicalProjectionUniform.inverseGramFunction R θ) :=
    funext (fun θ=>(PhysicalProjectionUniform.inverseGramFunction_eq hR θ.property).symm)
  rw [he]
  exact hh

theorem driveTop_continuous {R : ℝ} (hR : 0<R) (i : Index) :
    Continuous (fun θ : positiveDomain R=>driveTop hR θ.property i) := by
  have hr := rawTop_continuous hR i
  have hs := (sourceMap hR).continuous.comp hr
  have ha := (actual_analysis_continuous hR).clm_apply hs
  have hg := (inverseGram_continuous hR).clm_apply ha
  exact hr.sub ((actual_synthesis_continuous hR).clm_apply hg)

end
end Resonance.OnsagerDriveFamily
