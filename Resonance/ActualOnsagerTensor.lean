import Resonance.BoundedMicroProjection
import Resonance.CellResponse

/-! The manuscript's actual fifteen transport drives and response tensor.
The kernel, measure, projection, and weak inverse are the original objects. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.ActualOnsagerTensor
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalVariationalCell
open BoundedCellSource BoundedMicroProjection CellResponse

abbrev Index := Fin 3 × Fin 5

def rawDrive (θ : Parameter) (i : Index) (k : E) : ℝ := 2*k i.1*basisFunction θ i.2 k

theorem rawDrive_measurable (θ : Parameter) (i : Index) : Measurable (rawDrive θ i) :=
  (((PiLp.proj 2 (fun _ : Fin 3=>ℝ) i.1 : E→L[ℝ]ℝ).continuous.measurable).const_mul 2).mul
    (basis_measurable θ i.2)

theorem rawDrive_continuousOn {R : ℝ} {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) : ContinuousOn (rawDrive θ i) (cube R) :=
  (((PiLp.proj 2 (fun _ : Fin 3=>ℝ) i.1 : E→L[ℝ]ℝ).continuous.const_mul 2).continuousOn).mul
    (basis_continuousOn hθ i.2)

theorem rawDrive_memLp_top {R : ℝ} {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    MemLp (rawDrive θ i) ∞ (referenceMeasure R) :=
  continuous_cube_memLp_top (rawDrive_measurable θ i) (rawDrive_continuousOn hθ i)

def drive {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i : Index) : E→ℝ := projectDrive hR hθ (rawDrive_memLp_top hθ i)

theorem drive_memLp_top {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) : MemLp (drive hR hθ i) ∞ (referenceMeasure R) :=
  projectDrive_memLp_top hR hθ (rawDrive_memLp_top hθ i)

theorem drive_micro {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    projection hR hθ (boundedVector hR (drive_memLp_top hR hθ i))=0 :=
  projectDrive_micro hR hθ (rawDrive_memLp_top hθ i)

def source {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i : Index) : Space R→L[ℝ]ℝ := moment hR (drive_memLp_top hR hθ i)

def transportCell {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i : Index) : Micro hR hθ := solve hR hθ (source hR hθ i)

theorem transportCell_equation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) (v : Space R) :
    physicalForm hR.le hθ (transportCell hR hθ i) v=
      ∫k,v k*drive hR hθ i k∂cubeVolume R :=
  actual_bounded_cell_pairing hR hθ _ (drive_micro hR hθ i) v

theorem transportCell_unique {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) {u : Micro hR hθ}
    (hu : ∀v : Space R,physicalForm hR.le hθ u v=
      ∫k,v k*drive hR hθ i k∂cubeVolume R) : u=transportCell hR hθ i :=
  actual_bounded_cell_unique hR hθ _ hu

def tensor {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Matrix Index Index ℝ := fun i j=>response hR hθ (source hR hθ i) (source hR hθ j)

theorem tensor_original_integral {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i j : Index) :
    tensor hR hθ i j=∫k,(transportCell hR hθ j : Space R) k*drive hR hθ i k∂cubeVolume R :=
  moment_apply hR (drive_memLp_top hR hθ i) (transportCell hR hθ j)

theorem tensor_pairing_integrable {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i j : Index) :
    Integrable (fun k=>(transportCell hR hθ j : Space R) k*drive hR hθ i k) (cubeVolume R) :=
  weighted_moment_integrable hR (drive_memLp_top hR hθ i) (transportCell hR hθ j)

theorem tensor_gram {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i j : Index) :
    tensor hR hθ i j=physicalForm hR.le hθ (transportCell hR hθ i) (transportCell hR hθ j) :=
  response_as_form hR hθ _ _

theorem tensor_reciprocity {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i j : Index) : tensor hR hθ i j=tensor hR hθ j i :=
  response_symmetric hR hθ _ _

end
end Resonance.ActualOnsagerTensor
