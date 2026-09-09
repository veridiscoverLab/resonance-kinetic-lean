import Resonance.ContinuousSourceForm

/-! The same continuous representative of the actual bounded resolvent
satisfies I minus s times the original normalized collision derivative,
pointwise on the whole cube. -/
open Set MeasureTheory
namespace Resonance.ContinuousRegularizedEquation
noncomputable section
set_option maxHeartbeats 2200000
open ResonantMeasure Thermodynamics ProfileBanachSmooth
open ContinuousSourceCoordinates ContinuousSourceForm CubeLinftyCoordinates ActualPairNormalization
open RegularizedContinuousOutput ShiftedStrongCell RegularizedCellBounds
open PhysicalWeightedCoercivity PhysicalMomentProjection ReferenceFrequencySpace

def output {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F : C(cube R,ℝ)) : C(cube R,ℝ) :=
  continuousOutput hR hθ (inv_pos.mpr hs) F

theorem output_embed {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F : C(cube R,ℝ)) :
    embed R (output hR hθ hs F)=boundedOutput hR hθ (inv_nonneg.mpr hs.le) (embed R F) :=
  continuousOutput_embed hR hθ (inv_pos.mpr hs) F

theorem output_source {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F : C(cube R,ℝ)) :
    sourceMap hR (output hR hθ hs F)=
      s⁻¹ • shiftedCell hR hθ (inv_nonneg.mpr hs.le) (embed R F) := by
  apply Lp.ext
  apply (reference_volume_equivalent hR).2.ae_eq
  exact (sourceMap_ae hR (output hR hθ hs F)).trans
    (continuousOutput_is_actual_physical_vector hR hθ (inv_pos.mpr hs) F)

theorem output_micro {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F : C(cube R,ℝ))
    (hQ : projection hR hθ (sourceMap hR F)=0) :
    projection hR hθ (sourceMap hR (output hR hθ hs F))=0 := by
  rw [output_source,map_smul,shifted_cell_micro hR hθ _ (embed R F) hQ,smul_zero]

theorem output_weak_equation {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 0<s) (F v : C(cube R,ℝ))
    (hQ : projection hR hθ (sourceMap hR F)=0) :
    s*physicalForm hR.le hθ (sourceMap hR (output hR hθ hs F)) (sourceMap hR v)+
      ContinuousCollisionMoments.cubeIntegral R (v*output hR hθ hs F)=
        ContinuousCollisionMoments.cubeIntegral R (v*F) := by
  have hw := actual_regularized_pairing hR hθ hs (embed R F) hQ (sourceMap hR v)
  rw [←output_source hR hθ hs F] at hw
  have hout : (∫k,sourceMap hR v k*boundedOutput hR hθ (inv_nonneg.mpr hs.le) (embed R F) k∂cubeVolume R)=
      ContinuousCollisionMoments.cubeIntegral R (v*output hR hθ hs F) := by
    rw [←output_embed hR hθ hs F,←sourceMap_cube_pairing hR v (output hR hθ hs F)]
    apply integral_congr_ae
    filter_upwards [embed_ae R (output hR hθ hs F)] with k hk
    rw [hk]
  have hin : (∫k,sourceMap hR v k*embed R F k∂cubeVolume R)=
      ContinuousCollisionMoments.cubeIntegral R (v*F) := by
    rw [←sourceMap_cube_pairing hR v F]
    apply integral_congr_ae
    filter_upwards [embed_ae R F] with k hk
    rw [hk]
  rwa [hout,hin] at hw

theorem actual_continuous_regularized_equation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) (F : C(cube R,ℝ))
    (hQ : projection hR hθ (sourceMap hR F)=0) :
    output hR hθ hs F-s • (denominatorMap R θ*
      fderiv ℝ (FiberContinuity.collisionMap R hR.le) (profileMap R θ)
        (profileMap R θ*output hR hθ hs F))=F := by
  apply sub_eq_zero.mp
  apply cube_tests_separate hR
  intro v
  have hw := output_weak_equation hR hθ hs F v hQ
  have hf := normalized_derivative_pairing hR hθ (output hR hθ hs F) v
  have halg : v*(output hR hθ hs F-s • (denominatorMap R θ*
      fderiv ℝ (FiberContinuity.collisionMap R hR.le) (profileMap R θ)
        (profileMap R θ*output hR hθ hs F))-F)=
      v*output hR hθ hs F-s • (v*(denominatorMap R θ*
      fderiv ℝ (FiberContinuity.collisionMap R hR.le) (profileMap R θ)
        (profileMap R θ*output hR hθ hs F)))-v*F := by
    simp only [mul_sub,mul_smul_comm]
  rw [halg,map_sub,map_sub,map_smul,hf]
  simp only [smul_eq_mul]
  linarith

end
end Resonance.ContinuousRegularizedEquation
