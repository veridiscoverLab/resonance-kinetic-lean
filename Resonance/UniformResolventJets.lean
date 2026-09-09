import Resonance.UniformResolventSmooth
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Uniform parameter jets of the original shifted bounded resolvents.
The derivative is taken in the five original RJ parameters; z is kept
fixed. Constants are uniform over every compact positive parameter set
and the entire interval 0 <= z <= 1. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.UniformResolventJets
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace LinftyMultiplication
open UniformShiftSpace UniformShiftSmooth UniformResolventSmooth

def boundedFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : Family R :=
  (1-multiplierFamily hR θ)*coordinateFamily hR θ

theorem boundedFamily_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    boundedFamily hR θ z=RegularizedCellBounds.boundedOutput hR hθ z.property.1 := by
  change (1-multiplierFamily hR θ z)*coordinateFamily hR θ z=_
  rw [multiplierFamily_apply hR hθ,coordinateFamily_apply hR hθ]
  rfl

theorem boundedFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (boundedFamily hR) θ :=
  (contDiffAt_const.sub (multiplierFamily_contDiffAt hR hθ)).mul
    (coordinateFamily_contDiffAt hR hθ)

theorem weightedCellFamily_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) (F : X R) :
    weightedCellFamily hR θ z F=ᵐ[cubeVolume R] fun k=>
      referenceFrequency R k*ShiftedStrongCell.shiftedCell hR hθ z.property.1 F k := by
  change ratioFamily hR θ z (coordinateFamily hR θ z F)=ᵐ[cubeVolume R] _
  rw [ratioFamily_apply hR hθ,coordinateFamily_apply hR hθ]
  filter_upwards [ShiftRelativeAlgebra.ratioOp_ae hR hθ z.property.1
      (ShiftedParameterContinuity.shiftedCoordinate hR hθ z.property.1 F),
    PositiveLossShift.shiftedDivide_ae hR hθ z.property.1
      (ShiftedParameterContinuity.shiftedCoordinate hR hθ z.property.1 F)] with k hr hu
  change ShiftedStrongCell.shiftedCell hR hθ z.property.1 F k=_ at hu
  rw [hr,hu]
  ring

theorem compact_family_jet_bound {R : ℝ} {f : Parameter→Family R}
    (hf : ∀θ∈positiveDomain R,ContDiffAt ℝ ∞ f θ)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀z : Shift,
      ‖iteratedFDeriv ℝ n (fun β=>f β z) θ‖≤C := by
  have hc : ContinuousOn (fun θ=>iteratedFDeriv ℝ n f θ) K := by
    intro θ hθ
    exact ((hf θ (hpos hθ)).continuousAt_iteratedFDeriv
      (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc.norm
  let C := max M 0+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro θ hθ z
  have hb : ‖iteratedFDeriv ℝ n f θ‖≤C :=
    (hM ⟨θ,hθ,rfl⟩).trans (by dsimp [C]; linarith [le_max_left M 0])
  have he := (evalMap R z).norm_iteratedFDeriv_comp_left (hf θ (hpos hθ))
    (n:=n) (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))
  exact he.trans ((mul_le_mul (evalMap_norm_le R z) hb
    (norm_nonneg _) zero_le_one).trans_eq (one_mul C))

theorem actual_coordinate_jets_uniform {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀z : Shift,
      ‖iteratedFDeriv ℝ n (fun β=>coordinateFamily hR β z) θ‖≤C :=
  compact_family_jet_bound (fun _ hθ=>coordinateFamily_contDiffAt hR hθ) hK hpos n

theorem actual_weighted_jets_uniform {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀z : Shift,
      ‖iteratedFDeriv ℝ n (fun β=>weightedCellFamily hR β z) θ‖≤C :=
  compact_family_jet_bound (fun _ hθ=>weightedCellFamily_contDiffAt hR hθ) hK hpos n

theorem actual_bounded_jets_uniform {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀z : Shift,
      ‖iteratedFDeriv ℝ n (fun β=>boundedFamily hR β z) θ‖≤C :=
  compact_family_jet_bound (fun _ hθ=>boundedFamily_contDiffAt hR hθ) hK hpos n

end
end Resonance.UniformResolventJets
