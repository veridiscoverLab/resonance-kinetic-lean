import Resonance.UniformResolventJets

/-! The physical weighted-space readback of the same uniform shift
family, and its actual high parameter derivatives. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.UniformPhysicalCellJets
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace LinftyMultiplication
open UniformShiftSpace UniformResolventSmooth UniformResolventJets PhysicalDivideSmooth

def physicalLinear {R : ℝ} (hR : 0<R) : Op R→ₗ[ℝ](X R→L[ℝ]Space R) where
  toFun A := (referenceDivide hR).comp A
  map_add' A B := by ext F; simp
  map_smul' a A := by ext F; simp

def physicalMap {R : ℝ} (hR : 0<R) : Op R→L[ℝ](X R→L[ℝ]Space R) :=
  (physicalLinear hR).mkContinuous ‖referenceDivide hR‖ (fun A=>
    ContinuousLinearMap.opNorm_comp_le (referenceDivide hR) A)

theorem physicalMap_norm_le {R : ℝ} (hR : 0<R) : ‖physicalMap hR‖≤‖referenceDivide hR‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro A
  exact ContinuousLinearMap.opNorm_comp_le _ _

def physicalFamily {R : ℝ} (hR : 0<R) (θ : Parameter) (z : Shift) : X R→L[ℝ]Space R :=
  physicalMap hR (weightedCellFamily hR θ z)

theorem physicalFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    physicalFamily hR θ z=ShiftedStrongCell.shiftedCell hR hθ z.property.1 := by
  apply ContinuousLinearMap.ext
  intro F
  apply MeasureTheory.Lp.ext
  apply (reference_volume_equivalent hR).2.ae_eq
  filter_upwards [referenceDivide_ae hR (weightedCellFamily hR θ z F),
    weightedCellFamily_ae hR hθ z F,CornerInverseFrequency.referenceFrequency_positive_ae hR]
    with k hd hw hp
  change physicalFamily hR θ z F k=_ at hd
  rw [hd,hw]
  exact mul_div_cancel_left₀ _ hp.ne'

theorem physicalFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (z : Shift) :
    ContDiffAt ℝ ∞ (fun β=>physicalFamily hR β z) θ :=
  (physicalMap hR).contDiff.contDiffAt.comp θ
    ((evalMap R z).contDiff.contDiffAt.comp θ (weightedCellFamily_contDiffAt hR hθ))

theorem actual_physical_jets_uniform {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀z : Shift,
      ‖iteratedFDeriv ℝ n (fun β=>physicalFamily hR β z) θ‖≤C := by
  obtain ⟨B,hB,hb⟩ := actual_weighted_jets_uniform hR hK hpos n
  refine ⟨‖referenceDivide hR‖*B+1,by positivity,?_⟩
  intro θ hθ z
  have he := (physicalMap hR).norm_iteratedFDeriv_comp_left
    ((evalMap R z).contDiff.contDiffAt.comp θ (weightedCellFamily_contDiffAt hR (hpos hθ)))
    (n:=n) (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))
  apply he.trans
  exact (mul_le_mul (physicalMap_norm_le hR) (hb θ hθ z)
    (norm_nonneg _) (norm_nonneg _)).trans (le_add_of_nonneg_right zero_le_one)

end
end Resonance.UniformPhysicalCellJets
