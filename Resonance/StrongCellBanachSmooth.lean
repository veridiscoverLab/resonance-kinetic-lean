import Resonance.BasisBanachSmooth

/-! Smooth dependence of the actual augmented inverse and its physical
cell on the fixed original Banach spaces. Invertibility is inherited
from the proved original compact Fredholm argument, not assumed. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.StrongCellBanachSmooth
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open LinftyMultiplication BasisBanachSmooth ActualGainSmooth PhysicalDivideSmooth
open NormalizedLossSmooth

def augmentedFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]X R :=
  1+(gainFamily hR θ+(synthesisFamily R θ).comp ((analysisFamily hR θ).comp (divideMap hR θ)))

theorem augmentedFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    augmentedFamily hR θ=LinftyFiveAugmentation.augmented hR hθ := by
  rw [augmentedFamily,gainFamily_eq hR hθ,synthesisFamily_eq hθ,
    analysisFamily_eq hR hθ,divideMap_eq hR hθ]
  rfl

theorem augmentedFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (augmentedFamily hR) θ :=
  contDiffAt_const.add ((gainFamily_contDiffAt hR hθ).add
    ((synthesisFamily_contDiffAt hθ).clm_comp
      ((analysisFamily_contDiffAt hR hθ).clm_comp (divideMap_contDiffAt hR hθ))))

def actualAugmentedUnit {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    (X R→L[ℝ]X R)ˣ where
  val := augmentedFamily hR θ
  inv := StrongBoundedCell.coordinate hR hθ
  val_inv := by
    apply ContinuousLinearMap.ext
    intro f
    change augmentedFamily hR θ (StrongBoundedCell.coordinate hR hθ f)=f
    rw [augmentedFamily_eq hR hθ]
    exact StrongBoundedCell.augmented_coordinate hR hθ f
  inv_val := by
    apply ContinuousLinearMap.ext
    intro f
    change StrongBoundedCell.coordinate hR hθ (augmentedFamily hR θ f)=f
    rw [augmentedFamily_eq hR hθ]
    exact (LinftyFiveAugmentation.augmentedEquiv hR hθ).symm_apply_apply f

def coordinateFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]X R :=
  Ring.inverse (augmentedFamily hR θ)

theorem coordinateFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    coordinateFamily hR θ=StrongBoundedCell.coordinate hR hθ :=
  Ring.inverse_unit (actualAugmentedUnit hR hθ)

theorem coordinateFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (coordinateFamily hR) θ :=
  (contDiffAt_ringInverse (𝕜:=ℝ) (n:=∞) (actualAugmentedUnit hR hθ)).comp θ
    (augmentedFamily_contDiffAt hR hθ)

def cellFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]Space R :=
  (divideMap hR θ).comp (coordinateFamily hR θ)

theorem cellFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    cellFamily hR θ=StrongBoundedCell.cell hR hθ := by
  rw [cellFamily,divideMap_eq hR hθ,coordinateFamily_eq hR hθ]
  rfl

theorem cellFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (cellFamily hR) θ :=
  (divideMap_contDiffAt hR hθ).clm_comp (coordinateFamily_contDiffAt hR hθ)

def weightedCellFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]X R :=
  (inverseOperator hR.le θ).comp (coordinateFamily hR θ)

theorem weightedCellFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    weightedCellFamily hR θ=StrongCellWeightedContinuity.weightedCell hR hθ := by
  rw [weightedCellFamily,inverseOperator_eq_actual_multiplier hR hθ,coordinateFamily_eq hR hθ]
  rfl

theorem weightedCellFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (weightedCellFamily hR) θ :=
  (inverseOperator_contDiffAt hR hθ).clm_comp (coordinateFamily_contDiffAt hR hθ)

theorem actual_augmentedFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (augmentedFamily hR) (positiveDomain R) :=
  fun _ hθ=>(augmentedFamily_contDiffAt hR hθ).contDiffWithinAt

theorem actual_coordinateFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (coordinateFamily hR) (positiveDomain R) :=
  fun _ hθ=>(coordinateFamily_contDiffAt hR hθ).contDiffWithinAt

theorem actual_cellFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (cellFamily hR) (positiveDomain R) :=
  fun _ hθ=>(cellFamily_contDiffAt hR hθ).contDiffWithinAt

theorem actual_weightedCellFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (weightedCellFamily hR) (positiveDomain R) :=
  fun _ hθ=>(weightedCellFamily_contDiffAt hR hθ).contDiffWithinAt

end
end Resonance.StrongCellBanachSmooth
