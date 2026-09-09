import Resonance.UniformPhysicalCellJets

/-! Actual (I+s L_theta) inverse parameter jets with the manuscript's
two norms. No differentiability in s, no spectral gap, and no source
moment constraint are silently used in the parameter differentiation. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.RegularizedParameterJets
noncomputable section
set_option maxHeartbeats 2000000
open Thermodynamics LinftyMultiplication UniformShiftSpace UniformShiftSmooth
open UniformResolventSmooth UniformResolventJets UniformPhysicalCellJets
open ReferenceFrequencySpace

def inverseShift (s : ℝ) (hs : 1 ≤ s) : Shift :=
  ⟨s⁻¹,inv_nonneg.mpr (zero_le_one.trans hs),inv_le_one_of_one_le₀ hs⟩

def boundedMap {R : ℝ} (hR : 0<R) (θ : Parameter) (s : ℝ) (hs : 1 ≤ s) : Op R :=
  boundedFamily hR θ (inverseShift s hs)

def weightedMap {R : ℝ} (hR : 0<R) (θ : Parameter) (s : ℝ) (hs : 1 ≤ s) : Op R :=
  s⁻¹ • weightedCellFamily hR θ (inverseShift s hs)

def physicalMap {R : ℝ} (hR : 0<R) (θ : Parameter) (s : ℝ) (hs : 1 ≤ s) : X R→L[ℝ]Space R :=
  s⁻¹ • physicalFamily hR θ (inverseShift s hs)

theorem boundedMap_eq {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) :
    boundedMap hR θ s hs=RegularizedCellBounds.boundedOutput hR hθ
      (inv_nonneg.mpr (zero_le_one.trans hs)) := boundedFamily_apply hR hθ _

theorem physicalMap_eq {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) :
    physicalMap hR θ s hs=s⁻¹ • ShiftedStrongCell.shiftedCell hR hθ
      (inv_nonneg.mpr (zero_le_one.trans hs)) := by
  unfold physicalMap
  rw [physicalFamily_eq hR hθ]
  rfl

theorem physicalMap_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) (F : X R) :
    physicalMap hR θ s hs F=ᵐ[ActualPairNormalization.cubeVolume R] fun k=>
      s⁻¹*ShiftedStrongCell.shiftedCell hR hθ (inv_nonneg.mpr (zero_le_one.trans hs)) F k := by
  rw [physicalMap_eq hR hθ,ContinuousLinearMap.smul_apply]
  exact (reference_volume_equivalent hR).1.ae_eq (MeasureTheory.Lp.coeFn_smul _ _)

theorem boundedMap_same_physical {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) (F : X R) :
    boundedMap hR θ s hs F=ᵐ[ActualPairNormalization.cubeVolume R] physicalMap hR θ s hs F := by
  rw [boundedMap_eq hR hθ]
  exact (RegularizedCellBounds.boundedOutput_ae hR hθ _ F).trans (physicalMap_ae hR hθ s hs F).symm

theorem weightedMap_same_physical {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) (F : X R) :
    weightedMap hR θ s hs F=ᵐ[ActualPairNormalization.cubeVolume R] fun k=>
      CollisionFrequency.referenceFrequency R k*physicalMap hR θ s hs F k := by
  filter_upwards [MeasureTheory.Lp.coeFn_smul s⁻¹ (weightedCellFamily hR θ (inverseShift s hs) F),
    weightedCellFamily_ae hR hθ (inverseShift s hs) F,physicalMap_ae hR hθ s hs F]
    with k ha hw hu
  change weightedMap hR θ s hs F k=_ at ha
  simp only [Pi.smul_apply,smul_eq_mul] at ha
  rw [ha,hw,hu]
  dsimp only [inverseShift]
  ring

theorem actual_regularized_equation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) (F : X R)
    (hQ : PhysicalMomentProjection.projection hR hθ (StrongBoundedCell.sourceVector hR F)=0)
    (v : Space R) :
    s*PhysicalWeightedCoercivity.physicalForm hR.le hθ (physicalMap hR θ s hs F) v+
      (∫k,v k*boundedMap hR θ s hs F k∂ActualPairNormalization.cubeVolume R)=
        ∫k,v k*F k∂ActualPairNormalization.cubeVolume R := by
  rw [physicalMap_eq hR hθ,boundedMap_eq hR hθ,ContinuousLinearMap.smul_apply]
  exact RegularizedCellBounds.actual_regularized_pairing hR hθ (zero_lt_one.trans_le hs) F hQ v

theorem scalar_jet_bound {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Parameter→Y} {θ : Parameter} (hf : ContDiffAt ℝ ∞ f θ)
    (n : ℕ) {B s : ℝ} (hs : 0<s) (hb : ‖iteratedFDeriv ℝ n f θ‖≤B) :
    ‖iteratedFDeriv ℝ n (fun β=>s⁻¹ • f β) θ‖≤B/s := by
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le
    (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))),norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs.le)).trans_eq (by ring)

theorem actual_regularized_parameter_jets {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀(s : ℝ)(hs : 1 ≤ s),
      ‖iteratedFDeriv ℝ n (fun β=>boundedMap hR β s hs) θ‖≤C ∧
      ‖iteratedFDeriv ℝ n (fun β=>weightedMap hR β s hs) θ‖≤C/s ∧
      ‖iteratedFDeriv ℝ n (fun β=>physicalMap hR β s hs) θ‖≤C/s := by
  obtain ⟨A,hA,ha⟩ := actual_bounded_jets_uniform hR hK hpos n
  obtain ⟨B,hB,hb⟩ := actual_weighted_jets_uniform hR hK hpos n
  obtain ⟨D,hD,hd⟩ := actual_physical_jets_uniform hR hK hpos n
  let C := A+B+D
  have hAC : A≤C := by dsimp [C]; linarith
  have hBC : B≤C := by dsimp [C]; linarith
  have hDC : D≤C := by dsimp [C]; linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro θ hθ s hs
  have hs0 : 0<s := zero_lt_one.trans_le hs
  let z := inverseShift s hs
  refine ⟨(ha θ hθ z).trans hAC,?_,?_⟩
  · exact (scalar_jet_bound ((evalMap R z).contDiff.contDiffAt.comp θ
      (weightedCellFamily_contDiffAt hR (hpos hθ))) n hs0 (hb θ hθ z)).trans
        (div_le_div_of_nonneg_right hBC hs0.le)
  · exact (scalar_jet_bound (physicalFamily_contDiffAt hR (hpos hθ) z) n hs0
      (hd θ hθ z)).trans (div_le_div_of_nonneg_right hDC hs0.le)

end
end Resonance.RegularizedParameterJets
