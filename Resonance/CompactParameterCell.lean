import Resonance.DivideParameterContinuity
import Resonance.BasisParameterContinuity
import Resonance.StrongBoundedCell
import Mathlib.Analysis.Normed.Ring.Units

/-! The actual augmented inverse and the actual strong cell vary in
operator norm on compact subsets of the full positive parameter domain.
The resulting uniform estimate controls both H_nu and nu_* L-infinity. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.CompactParameterCell
noncomputable section
set_option maxHeartbeats 1400000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace PhysicalFiveBasis PhysicalMomentProjection
open LinftyFiveAugmentation StrongBoundedCell LinftyPhysicalDomain
open LinftyParameterContinuity BasisParameterContinuity DivideParameterContinuity

theorem subtype_continuous_of_bound {S : Set Parameter} {B : Type*}
    [NormedAddCommGroup B] {f : S→B} {C : ℝ} (hC : 0≤C)
    (hb : ∀x y : S,‖f x-f y‖≤C*‖(x:Parameter)-(y:Parameter)‖) : Continuous f := by
  have hl : LipschitzWith ⟨C,hC⟩ f := LipschitzWith.of_dist_le_mul (fun x y=>by
    simpa only [dist_eq_norm,Subtype.dist_eq,NNReal.coe_mk] using hb x y)
  exact hl.continuous

theorem compact_divide_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>divide hR (hpos θ.property)) := by
  obtain ⟨C,hC,hb⟩ := compact_divide_difference_bound hR hK hpos
  exact subtype_continuous_of_bound hC (fun x y=>hb x x.property y y.property)

theorem compact_analysis_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>analysisMap hR (hpos θ.property)) := by
  obtain ⟨C,hC,hb⟩ := compact_analysis_difference_bound hR hK hpos
  exact subtype_continuous_of_bound hC (fun x y=>hb x x.property y y.property)

theorem compact_synthesis_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>synthesisTop (hpos θ.property)) := by
  obtain ⟨C,hC,hb⟩ := compact_synthesis_difference_bound hR.le hK hpos
  exact subtype_continuous_of_bound hC (fun x y=>hb x x.property y y.property)

theorem compact_operator_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>AmbientLinftyCompact.operator hR (hpos θ.property)) := by
  obtain ⟨C,hC,hb⟩ := compact_operator_difference_bound hR hK hpos
  exact subtype_continuous_of_bound hC (fun x y=>hb x x.property y y.property)

theorem compact_augmented_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>augmented hR (hpos θ.property)) := by
  exact continuous_const.add ((compact_operator_continuous hR hK hpos).add
    ((compact_synthesis_continuous hR hK hpos).clm_comp
      ((compact_analysis_continuous hR hK hpos).clm_comp (compact_divide_continuous hR hK hpos))))

theorem coordinate_eq_ring_inverse {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    coordinate hR hθ=Ring.inverse (augmented hR hθ) := by
  have he := Ring.inverse_unit (augmentedEquiv hR hθ).toUnit
  exact he.symm

theorem compact_coordinate_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>coordinate hR (hpos θ.property)) := by
  simp_rw [coordinate_eq_ring_inverse]
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hi : ContinuousAt Ring.inverse (augmented hR (hpos θ.property)) :=
    NormedRing.inverse_continuousAt (augmentedEquiv hR (hpos θ.property)).toUnit
  exact ContinuousAt.comp (f:=fun β : K=>augmented hR (hpos β.property))
    (g:=Ring.inverse) hi (compact_augmented_continuous hR hK hpos).continuousAt

theorem compact_cell_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun θ : K=>StrongBoundedCell.cell hR (hpos θ.property)) :=
  (compact_divide_continuous hR hK hpos).clm_comp (compact_coordinate_continuous hR hK hpos)

theorem compact_cell_joint_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun z : K×Lp ℝ ∞ (cubeVolume R)=>
      StrongBoundedCell.cell hR (hpos z.1.property) z.2) :=
  ((compact_cell_continuous hR hK hpos).comp continuous_fst).clm_apply continuous_snd

theorem compact_coordinate_uniform_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀(θ : Parameter)(hθ : θ∈K)(F : Lp ℝ ∞ (cubeVolume R)),
      ‖coordinate hR (hpos hθ) F‖≤C*‖F‖ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M,hM⟩ := (isCompact_univ.image (compact_coordinate_continuous hR hK hpos).norm).bddAbove
  refine ⟨max M 0+1,by positivity,?_⟩
  intro θ hθ F
  apply ((coordinate hR (hpos hθ)).le_opNorm F).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
  exact (hM ⟨⟨θ,hθ⟩,mem_univ _,rfl⟩).trans (by linarith [le_max_left M 0])

theorem compact_cell_Hnu_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀(θ : Parameter)(hθ : θ∈K)(F : Lp ℝ ∞ (cubeVolume R)),
      ‖StrongBoundedCell.cell hR (hpos hθ) F‖≤C*‖F‖ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M,hM⟩ := (isCompact_univ.image (compact_cell_continuous hR hK hpos).norm).bddAbove
  refine ⟨max M 0+1,by positivity,?_⟩
  intro θ hθ F
  apply ((StrongBoundedCell.cell hR (hpos hθ)).le_opNorm F).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
  exact (hM ⟨⟨θ,hθ⟩,mem_univ _,rfl⟩).trans (by linarith [le_max_left M 0])

theorem compact_loss_reference_lower {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃a : ℝ,0<a ∧ ∀θ∈K,∀k∈cube R,a*referenceFrequency R k≤lossFrequency R (profile θ) k := by
  obtain ⟨a,b,C,ha,hb,hC,hl,hd⟩ := FrequencyParameterBounds.compact_loss_difference_bound hR.le hK hpos
  refine ⟨a/(1+9*R^2),div_pos ha (by positivity),?_⟩
  intro θ hθ k hk
  calc
    _ ≤ (a/(1+9*R^2))*((1+9*R^2)*geometricFrequency R k) :=
      mul_le_mul_of_nonneg_left (referenceFrequency_geometric_bounds hR.le hk).2 (by positivity)
    _ = a*geometricFrequency R k := by field_simp
    _ ≤ _ := (hl θ hθ k hk).1

theorem compact_cell_two_norm_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀(θ : Parameter)(hθ : θ∈K)(F : Lp ℝ ∞ (cubeVolume R)),
      ‖StrongBoundedCell.cell hR (hpos hθ) F‖≤C*‖F‖ ∧
      MemLp (fun k=>referenceFrequency R k*StrongBoundedCell.cell hR (hpos hθ) F k)
        ∞ (cubeVolume R) ∧
      ∀ᵐk∂cubeVolume R,
        ‖referenceFrequency R k*StrongBoundedCell.cell hR (hpos hθ) F k‖≤C*‖F‖ := by
  obtain ⟨C0,hC0,hcoord⟩ := compact_coordinate_uniform_bound hR hK hpos
  obtain ⟨C1,hC1,hcell⟩ := compact_cell_Hnu_bound hR hK hpos
  obtain ⟨a,ha,hlower⟩ := compact_loss_reference_lower hR hK hpos
  let C := C1+a⁻¹*C0
  have hC : 0<C := add_pos hC1 (mul_pos (inv_pos.mpr ha) hC0)
  refine ⟨C,hC,?_⟩
  intro θ hθ F
  have hAE : ∀ᵐk∂cubeVolume R,
      ‖referenceFrequency R k*StrongBoundedCell.cell hR (hpos hθ) F k‖≤C*‖F‖ := by
    filter_upwards [coordinate_frequency hR (hpos hθ) F,
      LinftyRowOperator.ae_norm_bound (coordinate hR (hpos hθ) F),
      ae_restrict_mem (measurable_cube R),loss_positive_ae hR (hpos hθ),
      CornerInverseFrequency.referenceFrequency_positive_ae hR] with k he hb hk hn hr
    have hc : ‖coordinate hR (hpos hθ) F k‖≤C0*‖F‖ := hb.trans (hcoord θ hθ F)
    have hν : referenceFrequency R k≤a⁻¹*lossFrequency R (profile θ) k := by
      calc
        _ = a⁻¹*(a*referenceFrequency R k) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hlower θ hθ k hk) (inv_nonneg.mpr ha.le)
    rw [norm_mul,Real.norm_of_nonneg hr.le]
    calc
      _ ≤ (a⁻¹*lossFrequency R (profile θ) k)*‖StrongBoundedCell.cell hR (hpos hθ) F k‖ :=
        mul_le_mul_of_nonneg_right hν (norm_nonneg _)
      _ = a⁻¹*‖coordinate hR (hpos hθ) F k‖ := by rw [←he,norm_mul,Real.norm_of_nonneg hn.le]; ring
      _ ≤ a⁻¹*(C0*‖F‖) := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr ha.le)
      _ ≤ C*‖F‖ := by dsimp [C]; nlinarith [mul_nonneg hC1.le (norm_nonneg F)]
  refine ⟨(hcell θ hθ F).trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr ha.le) hC0.le)) (norm_nonneg F)),?_,hAE⟩
  exact memLp_top_of_bound
    ((CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable).mul
      (Lp.stronglyMeasurable (StrongBoundedCell.cell hR (hpos hθ) F)).measurable).aestronglyMeasurable
    (C*‖F‖) hAE

/-- The compatible source produces the actual unique full-form cell,
with one constant controlling both spaces on the original parameter set. -/
theorem actual_compact_strong_cell {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀(θ : Parameter)(hθ : θ∈K)(F : Lp ℝ ∞ (cubeVolume R)),
      projection hR (hpos hθ) (sourceVector hR F)=0 →
      let u := StrongBoundedCell.cell hR (hpos hθ) F
      projection hR (hpos hθ) u=0 ∧
      (∀v : Space R,PhysicalWeightedCoercivity.physicalForm hR.le (hpos hθ) u v=
        ∫k,v k*F k∂cubeVolume R) ∧
      ‖u‖≤C*‖F‖ ∧ MemLp (fun k=>referenceFrequency R k*u k) ∞ (cubeVolume R) ∧
      (∀ᵐk∂cubeVolume R,‖referenceFrequency R k*u k‖≤C*‖F‖) ∧
      (∀w : Space R,projection hR (hpos hθ) w=0 →
        (∀v : Space R,PhysicalWeightedCoercivity.physicalForm hR.le (hpos hθ) w v=
          ∫k,v k*F k∂cubeVolume R) → w=u) := by
  obtain ⟨C,hC,hb⟩ := compact_cell_two_norm_bound hR hK hpos
  refine ⟨C,hC,?_⟩
  intro θ hθ F hQ
  exact ⟨cell_micro hR (hpos hθ) F hQ,actual_cell_pairing hR (hpos hθ) F hQ,
    (hb θ hθ F).1,(hb θ hθ F).2.1,(hb θ hθ F).2.2,fun w hw hpair=>by
      have he := congrArg Subtype.val (BoundedCellSource.actual_bounded_cell_unique hR (hpos hθ)
        (source_memLp_reference hR F) (u:=⟨w,hw⟩) hpair)
      exact he.trans (cell_eq_weak hR (hpos hθ) F hQ).symm⟩

end
end Resonance.CompactParameterCell
