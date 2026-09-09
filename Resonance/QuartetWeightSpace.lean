import Resonance.PhysicalDivideSmooth

/-! Continuous weights on the full four-leg cube, with a linear, Borel
zero extension retaining every original sharp flag. -/
open MeasureTheory Set
open scoped ENNReal ContDiff BigOperators
namespace Resonance.QuartetWeightSpace
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure
open CoareaNormalization (allFourFlags allFourFlags_measurable)
open Thermodynamics WeightedJointMeasure ProfileBanachSmooth

abbrev WeightSpace (R : ℝ) := C(Fin 4→cube R,ℝ)

def coordinates {R : ℝ} (q : allFourFlags R) : Fin 4→cube R := fun i=>⟨q.1 i,q.2 i⟩

theorem coordinates_continuous (R : ℝ) : Continuous (coordinates (R:=R)) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

def rawWeight (R : ℝ) (W : WeightSpace R) : FourMomenta→ℝ :=
  Function.extend Subtype.val (fun q : allFourFlags R=>W (coordinates q)) (fun _=>0)

theorem rawWeight_inside (R : ℝ) (W : WeightSpace R) {q : FourMomenta}
    (hq : q∈allFourFlags R) : rawWeight R W q=W (coordinates ⟨q,hq⟩) := by
  exact Subtype.val_injective.extend_apply (fun a : allFourFlags R=>W (coordinates a))
    (fun _=>0) ⟨q,hq⟩

theorem rawWeight_outside (R : ℝ) (W : WeightSpace R) {q : FourMomenta}
    (hq : q∉allFourFlags R) : rawWeight R W q=0 := by
  unfold rawWeight
  apply Function.extend_apply'
  rintro ⟨a,ha⟩
  exact hq (ha ▸ a.property)

theorem rawWeight_measurable (R : ℝ) (W : WeightSpace R) : Measurable (rawWeight R W) :=
  (MeasurableEmbedding.subtype_coe (allFourFlags_measurable R)).measurable_extend
    (W.continuous.comp (coordinates_continuous R)).measurable measurable_const

theorem rawWeight_add (R : ℝ) (V W : WeightSpace R) (q : FourMomenta) :
    rawWeight R (V+W) q=rawWeight R V q+rawWeight R W q := by
  by_cases hq : q∈allFourFlags R
  · rw [rawWeight_inside R _ hq,rawWeight_inside R _ hq,rawWeight_inside R _ hq]
    rfl
  · rw [rawWeight_outside R _ hq,rawWeight_outside R _ hq,rawWeight_outside R _ hq,add_zero]

theorem rawWeight_smul (R : ℝ) (c : ℝ) (W : WeightSpace R) (q : FourMomenta) :
    rawWeight R (c • W) q=c*rawWeight R W q := by
  by_cases hq : q∈allFourFlags R
  · rw [rawWeight_inside R _ hq,rawWeight_inside R _ hq]
    rfl
  · rw [rawWeight_outside R _ hq,rawWeight_outside R _ hq,mul_zero]

theorem rawWeight_one_nonnegative (R : ℝ) (q : FourMomenta) : 0≤rawWeight R 1 q := by
  by_cases hq : q∈allFourFlags R
  · rw [rawWeight_inside R _ hq]; norm_num
  · rw [rawWeight_outside R _ hq]

theorem rawWeight_bound (R : ℝ) (W : WeightSpace R) (q : FourMomenta) :
    ‖rawWeight R W q‖≤‖W‖*rawWeight R 1 q := by
  by_cases hq : q∈allFourFlags R
  · rw [rawWeight_inside R _ hq,rawWeight_inside R _ hq]
    simpa using W.norm_coe_le_norm (coordinates ⟨q,hq⟩)
  · rw [rawWeight_outside R _ hq,rawWeight_outside R _ hq,norm_zero,mul_zero]

theorem rawWeight_norm_bound (R : ℝ) (W : WeightSpace R) (q : FourMomenta) :
    ‖rawWeight R W q‖≤‖W‖ := by
  by_cases hq : q∈allFourFlags R
  · rw [rawWeight_inside R _ hq]
    exact W.norm_coe_le_norm _
  · rw [rawWeight_outside R _ hq,norm_zero]
    exact norm_nonneg _

def legLinear (R : ℝ) (i : Fin 4) : C(cube R,ℝ)→ₗ[ℝ]WeightSpace R where
  toFun f := ⟨fun q=>f (q i),f.continuous.comp (continuous_apply i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def legPullback (R : ℝ) (i : Fin 4) : C(cube R,ℝ)→L[ℝ]WeightSpace R :=
  (legLinear R i).mkContinuous 1 (fun f=>by
    apply (ContinuousMap.norm_le _ (by positivity : 0≤1*‖f‖)).mpr
    intro q
    simpa using f.norm_coe_le_norm (q i))

def profileWeightMap (R : ℝ) (θ : Parameter) : WeightSpace R :=
  ∏i : Fin 4,legPullback R i (profileMap R θ)

theorem profileWeightMap_apply {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    (q : Fin 4→cube R) : profileWeightMap R θ q=∏i : Fin 4,profile θ (q i) := by
  simp [profileWeightMap,legPullback,legLinear,profileMap_apply hθ]

theorem profileWeightMap_contDiffAt {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ContDiffAt ℝ ∞ (profileWeightMap R) θ := by
  apply contDiffAt_prod
  intro i _
  exact (legPullback R i).contDiff.contDiffAt.comp θ (profileMap_contDiffAt hθ)

theorem actual_profileWeightMap_contDiffOn (R : ℝ) :
    ContDiffOn ℝ ∞ (profileWeightMap R) (positiveDomain R) :=
  fun _ hθ=>(profileWeightMap_contDiffAt hθ).contDiffWithinAt

end
end Resonance.QuartetWeightSpace
