import Resonance.PhysicalMicroCoercivity
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! The actual weak cell inverse on the original microspace. Coercivity
is supplied by the original full-form theorem, not by a solver hypothesis. -/
open MeasureTheory Set
namespace Resonance.PhysicalVariationalCell
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalMomentProjection
open PhysicalProjectionKernel

def Micro {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) : Submodule ℝ (Space R) :=
  (projection hR hθ).ker

theorem micro_complete {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : CompleteSpace (Micro hR hθ) :=
  (projection hR hθ).isClosed_ker.completeSpace_coe

def microDifference {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Micro hR hθ→L[ℝ]FrequencyWeightedForm.J R θ :=
  (physicalDifference hR.le hθ).comp (projection hR hθ).ker.subtypeL

def microBilin {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Micro hR hθ→L[ℝ]Micro hR hθ→L[ℝ]ℝ :=
  (innerSL ℝ).bilinearComp (microDifference hR hθ) (microDifference hR hθ)

theorem microBilin_apply {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u v : Micro hR hθ) : microBilin hR hθ u v=physicalForm hR.le hθ u v := rfl

theorem actual_microBilin_coercive {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : IsCoercive (microBilin hR hθ) := by
  obtain ⟨δ,C,hδ,_hC,hgap⟩ := PhysicalMicroCoercivity.actual_microcoercivity hR
    (K:={θ}) isCompact_singleton (by intro β hβ; simpa only [mem_singleton_iff.mp hβ] using hθ)
  refine ⟨δ,hδ,?_⟩
  intro u
  have hg := (hgap θ (mem_singleton θ) u u.property).1
  change δ * ‖u‖ * ‖u‖ ≤ physicalForm hR.le hθ u u
  simpa only [pow_two,mul_assoc] using hg

def microEquiv {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Micro hR hθ≃L[ℝ]Micro hR hθ :=
  @IsCoercive.continuousLinearEquivOfBilin (Micro hR hθ) _ _ (micro_complete hR hθ)
    (microBilin hR hθ) (actual_microBilin_coercive hR hθ)

theorem microEquiv_pairing {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u v : Micro hR hθ) : inner ℝ (microEquiv hR hθ u) v=physicalForm hR.le hθ u v :=
  @IsCoercive.continuousLinearEquivOfBilin_apply (Micro hR hθ) _ _
    (micro_complete hR hθ) (microBilin hR hθ) (actual_microBilin_coercive hR hθ) u v

def microRiesz {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Micro hR hθ≃L[ℝ](Micro hR hθ→L[ℝ]ℝ) :=
  (@InnerProductSpace.toDual ℝ (Micro hR hθ) _ _ _
    (micro_complete hR hθ)).toContinuousLinearEquiv

theorem microRiesz_pairing {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (l : Micro hR hθ→L[ℝ]ℝ) (v : Micro hR hθ) :
    inner ℝ ((microRiesz hR hθ).symm l) v=l v :=
  @InnerProductSpace.toDual_symm_apply ℝ (Micro hR hθ) _ _ _ (micro_complete hR hθ) v l

def solve {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (source : Space R→L[ℝ]ℝ) : Micro hR hθ :=
  (microEquiv hR hθ).symm ((microRiesz hR hθ).symm
    (source.comp (projection hR hθ).ker.subtypeL))

theorem solve_micro_pairing {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (source : Space R→L[ℝ]ℝ) (v : Micro hR hθ) :
    physicalForm hR.le hθ (solve hR hθ source) v=source v := by
  rw [←microEquiv_pairing,solve,ContinuousLinearEquiv.apply_symm_apply,microRiesz_pairing]
  rfl

theorem solve_full_pairing {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (source : Space R→L[ℝ]ℝ) (hsource : ∀v∈(physicalDifference hR.le hθ).ker,source v=0)
    (v : Space R) : physicalForm hR.le hθ (solve hR hθ source) v=source v := by
  let w : Micro hR hθ := ⟨v-projection hR hθ v,by
    change projection hR hθ (v-projection hR hθ v)=0
    rw [map_sub,projection_idempotent,sub_self]⟩
  have hh := solve_micro_pairing hR hθ source w
  have hz := projection_difference_zero hR hθ v
  have hsz := hsource (projection hR hθ v) hz
  have hd : physicalDifference hR.le hθ (w : Space R)=physicalDifference hR.le hθ v := by
    change physicalDifference hR.le hθ (v-projection hR hθ v)=_
    rw [map_sub,hz,sub_zero]
  change inner ℝ (physicalDifference hR.le hθ (solve hR hθ source : Space R))
    (physicalDifference hR.le hθ (w : Space R))=source (w : Space R) at hh
  rw [hd] at hh
  change physicalForm hR.le hθ (solve hR hθ source) v=source (v-projection hR hθ v) at hh
  rwa [map_sub,hsz,sub_zero] at hh

theorem solve_unique {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (source : Space R→L[ℝ]ℝ) {u : Micro hR hθ}
    (hu : ∀v : Micro hR hθ,physicalForm hR.le hθ u v=source v) : u=solve hR hθ source := by
  apply (microEquiv hR hθ).injective
  apply ext_inner_right ℝ
  intro v
  rw [microEquiv_pairing,microEquiv_pairing,hu,solve_micro_pairing]

end
end Resonance.PhysicalVariationalCell
