import Resonance.ContinuousLinearizedUniqueness
import Resonance.BasisBanachSmooth

/-! The actual all-source augmented regularized operator on C(D).
This supplies a genuine Banach-algebra inverse for parameter calculus;
compatibility is required only when removing the five-moment augmentation. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace Resonance.ContinuousAugmentedResolvent
noncomputable section
set_option maxHeartbeats 2500000
open ResonantMeasure Thermodynamics ProfileBanachSmooth ContinuousSourceCoordinates
open ContinuousSourceForm ContinuousCollisionMoments PhysicalWeightedCoercivity
open ContinuousRegularizedEquation ContinuousLinearizedUniqueness
open CubeLinftyCoordinates CubeContinuousEssentialNorm ActualPairNormalization
open PhysicalFiveBasis LinftyFiveAugmentation ShiftedStrongCell
open BasisBanachSmooth

abbrev X (R : ℝ) := C(cube R,ℝ)

def correctionMap {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]X R :=
  (synthesisContinuousFamily R θ).comp ((analysisFamily hR θ).comp (sourceMap hR))

def augmented {R : ℝ} (hR : 0<R) (θ : Parameter) (s : ℝ) : X R→L[ℝ]X R :=
  1-s • linearAction hR.le θ+s • correctionMap hR θ

theorem synthesisContinuousFamily_eq {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    synthesisContinuousFamily R θ=synthesisContinuous hθ := by
  unfold synthesisContinuousFamily synthesisContinuous
  apply Finset.sum_congr rfl
  intro i _
  rw [basisContinuous_eq hθ]

theorem embed_pairing {R : ℝ} (hR : 0<R) (u v : X R) :
    (∫k,sourceMap hR u k*embed R v k∂cubeVolume R)=cubeIntegral R (u*v) := by
  rw [←sourceMap_cube_pairing hR u v]
  apply integral_congr_ae
  filter_upwards [embed_ae R v] with k hk
  rw [hk]

theorem correction_pairing {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (q v : X R) :
    cubeIntegral R (v*correctionMap hR θ q)=
      ∑i : Fin 5,(analysisMap hR hθ (sourceMap hR q)) i*(analysisMap hR hθ (sourceMap hR v)) i := by
  have he : correctionMap hR θ q=synthesisContinuous hθ (analysisMap hR hθ (sourceMap hR q)) := by
    unfold correctionMap
    rw [synthesisContinuousFamily_eq hθ,analysisFamily_eq hR hθ]
    rfl
  rw [he,←embed_pairing hR]
  exact synthesisTop_pairing hR hθ (sourceMap hR v) _

theorem augmented_pairing {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (s : ℝ) (q v : X R) :
    cubeIntegral R (v*augmented hR θ s q)=cubeIntegral R (v*q)+
      s*physicalForm hR.le hθ (sourceMap hR q) (sourceMap hR v)+
        s*∑i : Fin 5,(analysisMap hR hθ (sourceMap hR q)) i*(analysisMap hR hθ (sourceMap hR v)) i := by
  have he : v*augmented hR θ s q=v*q-s • (v*linearAction hR.le θ q)+s • (v*correctionMap hR θ q) := by
    change v*(q-s • linearAction hR.le θ q+s • correctionMap hR θ q)=_
    rw [mul_add,mul_sub,mul_smul_comm,mul_smul_comm]
  rw [he,map_add,map_sub,map_smul,map_smul,linearAction_pairing hR hθ,correction_pairing hR hθ]
  simp only [smul_eq_mul]
  ring

theorem output_augmented_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) (F v : X R) :
    cubeIntegral R (v*augmented hR θ s (output hR hθ hs F))=cubeIntegral R (v*F) := by
  let w := shiftedCell hR hθ (inv_nonneg.mpr hs.le) (embed R F)
  have hw : w=s • sourceMap hR (output hR hθ hs F) := by
    rw [output_source,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  have he := ShiftedAugmentation.shifted_pairing hR hθ (inv_nonneg.mpr hs.le)
    (ShiftedParameterContinuity.shiftedCoordinate hR hθ (inv_nonneg.mpr hs.le) (embed R F)) (sourceMap hR v)
  rw [shifted_augmented_coordinate] at he
  change (∫k,sourceMap hR v k*embed R F k∂cubeVolume R)=
    physicalForm hR.le hθ w (sourceMap hR v)+
      (∑i : Fin 5,(analysisMap hR hθ w) i*(analysisMap hR hθ (sourceMap hR v)) i)+
      (∫k,sourceMap hR v k*RegularizedCellBounds.boundedOutput hR hθ
        (inv_nonneg.mpr hs.le) (embed R F) k∂cubeVolume R) at he
  rw [hw,RegularizedCellBounds.physicalForm_smul_left hR hθ,
    map_smul,←output_embed hR hθ hs F,embed_pairing hR,embed_pairing hR] at he
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,←Finset.mul_sum] at he
  rw [augmented_pairing hR hθ]
  linarith

theorem augmented_output {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) (F : X R) :
    augmented hR θ s (output hR hθ hs F)=F := by
  apply sub_eq_zero.mp
  apply cube_tests_separate hR
  intro v
  rw [mul_sub,map_sub,output_augmented_pairing hR hθ hs,sub_self]

theorem augmented_injective {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0 ≤ s) : Function.Injective (augmented hR θ s) := by
  apply (injective_iff_map_eq_zero (augmented hR θ s)).mpr
  intro q hq
  have he := augmented_pairing hR hθ s q q
  rw [hq,mul_zero,map_zero] at he
  have hf : 0≤physicalForm hR.le hθ (sourceMap hR q) (sourceMap hR q) := by
    rw [physical_form_square]
    positivity
  have ha : 0≤∑i : Fin 5,(analysisMap hR hθ (sourceMap hR q)) i*(analysisMap hR hθ (sourceMap hR q)) i :=
    Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
  have hsq : 0≤cubeIntegral R (q*q) := integral_nonneg (fun k=>mul_self_nonneg (q k))
  apply cube_square_zero hR q
  nlinarith

theorem output_add {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F G : X R) : output hR hθ hs (F+G)=output hR hθ hs F+output hR hθ hs G := by
  apply augmented_injective hR hθ hs.le
  rw [map_add,augmented_output,augmented_output,augmented_output]

theorem output_smul {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (a : ℝ) (F : X R) : output hR hθ hs (a • F)=a • output hR hθ hs F := by
  apply augmented_injective hR hθ hs.le
  rw [map_smul,augmented_output,augmented_output]

def outputLinear {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) : X R→ₗ[ℝ]X R where
  toFun := output hR hθ hs
  map_add' := output_add hR hθ hs
  map_smul' := output_smul hR hθ hs

theorem output_bound {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F : X R) :
    ‖output hR hθ hs F‖≤‖RegularizedCellBounds.boundedOutput hR hθ (inv_nonneg.mpr hs.le)‖*‖F‖ := by
  rw [←embed_norm_eq hR,output_embed]
  exact ((RegularizedCellBounds.boundedOutput hR hθ _).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (extendVector_bound R F) (norm_nonneg _))

def outputCLM {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) : X R→L[ℝ]X R :=
  (outputLinear hR hθ hs).mkContinuous
    ‖RegularizedCellBounds.boundedOutput hR hθ (inv_nonneg.mpr hs.le)‖ (output_bound hR hθ hs)

def augmentedUnit {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) : (X R→L[ℝ]X R)ˣ where
  val := augmented hR θ s
  inv := outputCLM hR hθ hs
  val_inv := by
    apply ContinuousLinearMap.ext
    intro F
    exact augmented_output hR hθ hs F
  inv_val := by
    apply ContinuousLinearMap.ext
    intro F
    change output hR hθ hs (augmented hR θ s F)=F
    apply augmented_injective hR hθ hs.le
    exact augmented_output hR hθ hs (augmented hR θ s F)

end
end Resonance.ContinuousAugmentedResolvent
