import Resonance.LinftyFiveAugmentation
import Resonance.BoundedCellSource

/-! Strong weighted bounded cell for the actual sharp-cube operator.
The five-moment hypothesis is imposed on the original bounded source,
and the constructed strong solution is identified with the actual weak cell. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.StrongBoundedCell
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity ReferenceMomentFunctionals
open LinftyPhysicalDomain LinftyPhysicalForm LinftyFiveAugmentation

theorem source_memLp_reference {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) :
    MemLp (F : E→ℝ) ∞ (referenceMeasure R) :=
  memLp_top_of_bound (Lp.stronglyMeasurable F).measurable.aestronglyMeasurable ‖F‖
    ((reference_volume_equivalent hR).2.ae_le (LinftyRowOperator.ae_norm_bound F))

def sourceVector {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) : Space R :=
  BoundedCellSource.boundedVector hR (source_memLp_reference hR F)

def coordinate {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (augmentedEquiv hR hθ).symm.toContinuousLinearMap

def cell {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Space R := (divide hR hθ).comp (coordinate hR hθ)

theorem augmented_coordinate {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R)) :
    augmented hR hθ (coordinate hR hθ F)=F :=
  (augmentedEquiv hR hθ).apply_symm_apply F

theorem coordinate_frequency {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R)) :
    (fun k=>CollisionFrequency.lossFrequency R (profile θ) k*cell hR hθ F k)
      =ᵐ[cubeVolume R] coordinate hR hθ F := frequency_divide_ae hR hθ _

theorem cell_micro {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (sourceVector hR F)=0) :
    projection hR hθ (cell hR hθ F)=0 := by
  let u := cell hR hθ F
  let a := analysisMap hR hθ u
  have hp := projection_difference_zero hR hθ u
  have hz := BoundedCellSource.micro_source_annihilates_kernel hR hθ
    (source_memLp_reference hR F) hQ (projection hR hθ u) hp
  rw [moment_apply] at hz
  have he := augmented_pairing hR hθ (coordinate hR hθ F) (projection hR hθ u)
  rw [augmented_coordinate,hz,projection_moments] at he
  have hform : physicalForm hR.le hθ u (projection hR hθ u)=0 := by
    unfold physicalForm
    rw [hp,inner_zero_right]
  change 0=physicalForm hR.le hθ u (projection hR hθ u)+∑i : Fin 5,a i*a i at he
  rw [hform,zero_add] at he
  have ha : a=0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>mul_self_nonneg (a i))).mp
      he.symm i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hi
  change synthesis hR.le hθ (gramInverse hR hθ a)=0
  rw [ha,map_zero,map_zero]

theorem coordinate_equation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (sourceVector hR F)=0) :
    coordinate hR hθ F+AmbientLinftyCompact.operator hR hθ (coordinate hR hθ F)=F := by
  have ha : analysisMap hR hθ (cell hR hθ F)=0 := by
    rw [←projection_moments,cell_micro hR hθ F hQ,map_zero]
  have hc : correction hR hθ (coordinate hR hθ F)=0 := by
    change synthesisTop hθ (analysisMap hR hθ (cell hR hθ F))=0
    rw [ha,map_zero]
  have he := augmented_coordinate hR hθ F
  change coordinate hR hθ F+(AmbientLinftyCompact.operator hR hθ (coordinate hR hθ F)+
    correction hR hθ (coordinate hR hθ F))=F at he
  simpa only [hc,add_zero] using he

theorem actual_cell_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (sourceVector hR F)=0) (v : Space R) :
    physicalForm hR.le hθ (cell hR hθ F) v=∫k,v k*F k∂cubeVolume R := by
  have he := (actual_form_identity hR hθ (coordinate hR hθ F) v).2
  refine he.trans (integral_congr_ae ?_)
  have hsum := Lp.coeFn_add (coordinate hR hθ F)
    (AmbientLinftyCompact.operator hR hθ (coordinate hR hθ F))
  rw [coordinate_equation hR hθ F hQ] at hsum
  filter_upwards [hsum] with k hk
  change F k=coordinate hR hθ F k+
    AmbientLinftyCompact.operator hR hθ (coordinate hR hθ F) k at hk
  rw [hk]

theorem cell_eq_weak {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (sourceVector hR F)=0) :
    (cell hR hθ F : Space R)=
      BoundedCellSource.cell hR hθ (source_memLp_reference hR F) := by
  exact congrArg Subtype.val (BoundedCellSource.actual_bounded_cell_unique hR hθ
    (source_memLp_reference hR F)
    (u:=⟨cell hR hθ F,cell_micro hR hθ F hQ⟩) (actual_cell_pairing hR hθ F hQ))

theorem coordinate_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R)) :
    ‖coordinate hR hθ F‖≤‖coordinate hR hθ‖*‖F‖ := (coordinate hR hθ).le_opNorm F

theorem loss_weighted_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Lp ℝ ∞ (cubeVolume R)) :
    MemLp (fun k=>CollisionFrequency.lossFrequency R (profile θ) k*cell hR hθ F k)
      ∞ (cubeVolume R) ∧
    ∀ᵐ k∂cubeVolume R,‖CollisionFrequency.lossFrequency R (profile θ) k*cell hR hθ F k‖≤
      ‖coordinate hR hθ‖*‖F‖ := by
  refine ⟨(memLp_congr_ae (coordinate_frequency hR hθ F)).mpr
    (Lp.memLp (coordinate hR hθ F)),?_⟩
  filter_upwards [coordinate_frequency hR hθ F,LinftyRowOperator.ae_norm_bound
    (coordinate hR hθ F)] with k hk hb
  rw [hk]
  exact hb.trans (coordinate_bound hR hθ F)

theorem reference_weighted_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀F : Lp ℝ ∞ (cubeVolume R),
      MemLp (fun k=>CollisionFrequency.referenceFrequency R k*cell hR hθ F k)
        ∞ (cubeVolume R) ∧
      ∀ᵐ k∂cubeVolume R,‖CollisionFrequency.referenceFrequency R k*cell hR hθ F k‖≤C*‖F‖ := by
  obtain ⟨a,ha,hl⟩ := ActualFrequencyRatio.loss_reference_lower hR hθ
  refine ⟨a⁻¹*(‖coordinate hR hθ‖+1),mul_pos (inv_pos.mpr ha) (by positivity),?_⟩
  intro F
  have hb : ∀ᵐ k∂cubeVolume R,
      ‖CollisionFrequency.referenceFrequency R k*cell hR hθ F k‖≤
        (a⁻¹*(‖coordinate hR hθ‖+1))*‖F‖ := by
    filter_upwards [(loss_weighted_bound hR hθ F).2,
      CornerInverseFrequency.referenceFrequency_positive_ae hR,
      loss_positive_ae hR hθ,ae_restrict_mem (measurable_cube R)] with k hk hr hn hc
    have hcomp : CollisionFrequency.referenceFrequency R k≤
        a⁻¹*CollisionFrequency.lossFrequency R (profile θ) k := by
      have hh := hl k hc
      exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hh) |>.trans_eq (by ring)
    calc
      _ = CollisionFrequency.referenceFrequency R k*‖cell hR hθ F k‖ := by
        rw [norm_mul,Real.norm_of_nonneg hr.le]
      _ ≤ a⁻¹*(CollisionFrequency.lossFrequency R (profile θ) k*‖cell hR hθ F k‖) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcomp (norm_nonneg _)
      _ = a⁻¹*‖CollisionFrequency.lossFrequency R (profile θ) k*cell hR hθ F k‖ := by
        rw [norm_mul,Real.norm_of_nonneg hn.le]
      _ ≤ a⁻¹*(‖coordinate hR hθ‖*‖F‖) := mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr ha.le)
      _ ≤ _ := by nlinarith [inv_nonneg.mpr ha.le,norm_nonneg F]
  refine ⟨memLp_top_of_bound ?_ _ hb,hb⟩
  exact ((CollisionMarginalDensity.lossFrequency_measurable R
    CollisionFrequency.referenceProfile_continuous.measurable).mul
      (Lp.stronglyMeasurable (cell hR hθ F)).measurable).aestronglyMeasurable

theorem strong_bounded_cell {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀F : Lp ℝ ∞ (cubeVolume R),
      projection hR hθ (sourceVector hR F)=0 →
      ∃u : Space R,projection hR hθ u=0 ∧
        (∀v : Space R,physicalForm hR.le hθ u v=∫k,v k*F k∂cubeVolume R) ∧
        MemLp (fun k=>CollisionFrequency.referenceFrequency R k*u k) ∞ (cubeVolume R) ∧
        (∀ᵐ k∂cubeVolume R,‖CollisionFrequency.referenceFrequency R k*u k‖≤C*‖F‖) ∧
        (∀w : Space R,projection hR hθ w=0 →
          (∀v : Space R,physicalForm hR.le hθ w v=∫k,v k*F k∂cubeVolume R) → w=u) := by
  obtain ⟨C,hC,hb⟩ := reference_weighted_bound hR hθ
  refine ⟨C,hC,?_⟩
  intro F hQ
  refine ⟨cell hR hθ F,cell_micro hR hθ F hQ,actual_cell_pairing hR hθ F hQ,
    (hb F).1,(hb F).2,?_⟩
  intro w hw hpair
  have he := congrArg Subtype.val (BoundedCellSource.actual_bounded_cell_unique hR hθ
    (source_memLp_reference hR F) (u:=⟨w,hw⟩) hpair)
  exact he.trans (cell_eq_weak hR hθ F hQ).symm

end
end Resonance.StrongBoundedCell
