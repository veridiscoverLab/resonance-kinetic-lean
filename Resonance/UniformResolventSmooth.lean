import Resonance.UniformShiftSmooth

/-! Original shifted Fredholm inverses in the common supremum space.
The bounded inverse at each positive parameter is supplied by the actual
compact-shift theorem on [0,1], before Banach-algebra differentiation. -/
open Set
open scoped ENNReal ContDiff
namespace Resonance.UniformResolventSmooth
noncomputable section
set_option maxHeartbeats 1800000
open Thermodynamics LinftyMultiplication UniformShiftSpace UniformShiftSmooth
open StrongCellBanachSmooth ShiftedParameterContinuity

def augmentedFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : Family R :=
  1+constMap R (StrongCellBanachSmooth.augmentedFamily hR θ-1)*multiplierFamily hR θ

theorem augmentedFamily_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    augmentedFamily hR θ z=ShiftedAugmentation.shiftedAugmented hR hθ z.property.1 := by
  change 1+(StrongCellBanachSmooth.augmentedFamily hR θ-1)*multiplierFamily hR θ z=_
  rw [StrongCellBanachSmooth.augmentedFamily_eq hR hθ,multiplierFamily_apply hR hθ]
  simp only [LinftyFiveAugmentation.augmented,add_sub_cancel_left]
  rfl

theorem augmentedFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (augmentedFamily hR) θ :=
  contDiffAt_const.add (((constMap R).contDiff.contDiffAt.comp θ
    ((StrongCellBanachSmooth.augmentedFamily_contDiffAt hR hθ).sub contDiffAt_const)).mul
      (multiplierFamily_contDiffAt hR hθ))

theorem coordinate_uniform_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀z : Shift,‖shiftedCoordinate hR hθ z.property.1‖≤C := by
  have hpos : ({θ} : Set Parameter)⊆positiveDomain R := by
    intro β hβ
    simpa only [Set.mem_singleton_iff.mp hβ] using hθ
  obtain ⟨C,hC,hb⟩ := compact_shiftedCoordinate_uniform_bound hR isCompact_singleton hpos
    (Z:=1) zero_le_one
  refine ⟨C,hC,fun z=>?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro F
  exact hb θ (Set.mem_singleton θ) z z.property F

def coordinateBound {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) : ℝ :=
  (coordinate_uniform_bound hR hθ).choose

def actualCoordinateFamily {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Family R :=
  ofBound R (fun z=>shiftedCoordinate hR hθ z.property.1) (coordinateBound hR hθ)
    (coordinate_uniform_bound hR hθ).choose_spec.2

def actualUnit {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) : (Family R)ˣ where
  val := augmentedFamily hR θ
  inv := actualCoordinateFamily hR hθ
  val_inv := by
    apply lp.ext
    funext z
    change augmentedFamily hR θ z*shiftedCoordinate hR hθ z.property.1=1
    rw [augmentedFamily_apply hR hθ]
    apply ContinuousLinearMap.ext
    intro F
    exact (ShiftedAugmentation.shiftedEquiv hR hθ z.property.1).apply_symm_apply F
  inv_val := by
    apply lp.ext
    funext z
    change shiftedCoordinate hR hθ z.property.1*augmentedFamily hR θ z=1
    rw [augmentedFamily_apply hR hθ]
    apply ContinuousLinearMap.ext
    intro F
    exact (ShiftedAugmentation.shiftedEquiv hR hθ z.property.1).symm_apply_apply F

def coordinateFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : Family R :=
  Ring.inverse (augmentedFamily hR θ)

theorem coordinateFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    coordinateFamily hR θ=actualCoordinateFamily hR hθ := Ring.inverse_unit (actualUnit hR hθ)

theorem coordinateFamily_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    coordinateFamily hR θ z=shiftedCoordinate hR hθ z.property.1 := by
  rw [coordinateFamily_eq hR hθ]
  rfl

theorem coordinateFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (coordinateFamily hR) θ :=
  (contDiffAt_ringInverse (𝕜:=ℝ) (n:=∞) (actualUnit hR hθ)).comp θ
    (augmentedFamily_contDiffAt hR hθ)

def weightedCellFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : Family R :=
  ratioFamily hR θ*coordinateFamily hR θ

theorem weightedCellFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (weightedCellFamily hR) θ :=
  (ratioFamily_contDiffAt hR hθ).mul (coordinateFamily_contDiffAt hR hθ)

theorem actual_coordinateFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (coordinateFamily hR) (positiveDomain R) :=
  fun _ hθ=>(coordinateFamily_contDiffAt hR hθ).contDiffWithinAt

theorem actual_weightedCellFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (weightedCellFamily hR) (positiveDomain R) :=
  fun _ hθ=>(weightedCellFamily_contDiffAt hR hθ).contDiffWithinAt

end
end Resonance.UniformResolventSmooth
