import Resonance.PositiveShiftContinuity

/-! Joint continuity of the original shifted augmentation, including
zero shift, on compact positive parameter sets. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.ShiftedParameterContinuity
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics ActualPairNormalization ReferenceFrequencySpace
open PositiveLossShift ShiftedAugmentation PositiveShiftContinuity
open LinftyFiveAugmentation CompactParameterCell

theorem compact_norm_bound {X B : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup B] {f : X→B} (hf : Continuous f) :
    ∃M : ℝ,0≤M ∧ ∀x,‖f x‖≤M := by
  obtain ⟨M,hM⟩ := (isCompact_range hf.norm).bddAbove
  exact ⟨max M 0,le_max_right _ _,fun x=>(hM ⟨x,rfl⟩).trans (le_max_left _ _)⟩

theorem shifted_family_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : K→(Lp ℝ ∞ (cubeVolume R)→L[ℝ]Y))
    (hA : Continuous A) {C : ℝ} (hC : 0≤C)
    (hAb : ∀θ β : K,‖A θ-A β‖≤C*‖(θ:Parameter)-(β:Parameter)‖)
    (hz : ∀θ : K,Continuous (fun z : Set.Ici (0:ℝ)=>
      (A θ).comp (multiplier hR (hpos θ.property) z.property))) :
    Continuous (fun p : K×Set.Ici (0:ℝ)=>
      (A p.1).comp (multiplier hR (hpos p.1.property) p.2.property)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M,hM,hm⟩ := compact_norm_bound hA
  obtain ⟨C1,hC1,hb⟩ := compact_multiplier_difference_bound hR hK hpos
  apply continuous_prod_of_continuous_lipschitzWith _ ⟨C+M*C1,by positivity⟩ hz
  intro z
  apply LipschitzWith.of_dist_le_mul
  intro θ β
  simp only [dist_eq_norm,Subtype.dist_eq,NNReal.coe_mk]
  let Mθ := multiplier hR (hpos θ.property) z.property
  let Mβ := multiplier hR (hpos β.property) z.property
  have he : (A θ).comp Mθ-(A β).comp Mβ=
      (A θ-A β).comp Mθ+(A β).comp (Mθ-Mβ) := by
    ext f
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,map_sub]
    abel
  change ‖(A θ).comp Mθ-(A β).comp Mβ‖≤_
  rw [he]
  calc
    _ ≤ ‖(A θ-A β).comp Mθ‖+‖(A β).comp (Mθ-Mβ)‖ := norm_add_le _ _
    _ ≤ ‖A θ-A β‖*‖Mθ‖+‖A β‖*‖Mθ-Mβ‖ := add_le_add
      (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (C*‖(θ:Parameter)-(β:Parameter)‖)*1+
        M*(C1*‖(θ:Parameter)-(β:Parameter)‖) := add_le_add
      (mul_le_mul (hAb θ β) (multiplier_bound hR (hpos θ.property) z.property)
        (norm_nonneg _) (by positivity))
      (mul_le_mul (hm β) (hb θ θ.property β β.property z z.property)
        (norm_nonneg _) hM)
    _ = _ := by ring

theorem shiftedDivide_continuous {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Continuous (fun z : Set.Ici (0:ℝ)=>shiftedDivide hR hθ z.property) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : (w:ℝ)=0
  · have he : w=⟨0,show (0:ℝ)≤0 from le_rfl⟩ := Subtype.ext hw
    subst w
    change Tendsto _ _ _
    convert ShiftedDivideLimit.actual_shiftedDivide_continuousAt_zero hR hθ using 1
    congr 1
    change (LinftyPhysicalDomain.divide hR hθ).comp
      (multiplier hR hθ (show (0:ℝ)≤0 from le_rfl))=_
    rw [multiplier_zero]
    ext f
    rfl
  · exact continuousAt_const.clm_comp (multiplier_continuousAt_pos hR hθ w
      (lt_of_le_of_ne w.property (Ne.symm hw)))

theorem shiftedOperator_continuous {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Continuous (fun z : Set.Ici (0:ℝ)=>(AmbientLinftyCompact.operator hR hθ).comp
      (multiplier hR hθ z.property)) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : (w:ℝ)=0
  · have he : w=⟨0,show (0:ℝ)≤0 from le_rfl⟩ := Subtype.ext hw
    subst w
    change Tendsto _ _ _
    convert ShiftedOperatorLimit.actual_shifted_operator_continuousAt_zero hR hθ using 1
    congr 1
    change (AmbientLinftyCompact.operator hR hθ).comp
      (multiplier hR hθ (show (0:ℝ)≤0 from le_rfl))=_
    rw [multiplier_zero]
    ext f
    rfl
  · exact continuousAt_const.clm_comp (multiplier_continuousAt_pos hR hθ w
      (lt_of_le_of_ne w.property (Ne.symm hw)))

theorem compact_shiftedDivide_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun p : K×Set.Ici (0:ℝ)=>shiftedDivide hR (hpos p.1.property) p.2.property) := by
  obtain ⟨C,hC,hb⟩ := DivideParameterContinuity.compact_divide_difference_bound hR hK hpos
  exact shifted_family_continuous hR hK hpos _ (compact_divide_continuous hR hK hpos)
    hC (fun θ β=>hb θ θ.property β β.property) (fun θ=>shiftedDivide_continuous hR (hpos θ.property))

theorem compact_shiftedOperator_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun p : K×Set.Ici (0:ℝ)=>(AmbientLinftyCompact.operator hR (hpos p.1.property)).comp
      (multiplier hR (hpos p.1.property) p.2.property)) := by
  obtain ⟨C,hC,hb⟩ := LinftyParameterContinuity.compact_operator_difference_bound hR hK hpos
  exact shifted_family_continuous hR hK hpos _ (compact_operator_continuous hR hK hpos)
    hC (fun θ β=>hb θ θ.property β β.property) (fun θ=>shiftedOperator_continuous hR (hpos θ.property))

theorem compact_shiftedAugmented_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun p : K×Set.Ici (0:ℝ)=>shiftedAugmented hR (hpos p.1.property) p.2.property) := by
  have hs := (compact_synthesis_continuous hR hK hpos).comp
    (continuous_fst : Continuous (Prod.fst : K×Set.Ici (0:ℝ)→K))
  have ha := (compact_analysis_continuous hR hK hpos).comp
    (continuous_fst : Continuous (Prod.fst : K×Set.Ici (0:ℝ)→K))
  have hc := (continuous_const (y:=(1 : Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R)))).add
    ((compact_shiftedOperator_continuous hR hK hpos).add
    (hs.clm_comp (ha.clm_comp (compact_shiftedDivide_continuous hR hK hpos))))
  convert hc using 1

def shiftedCoordinate {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (shiftedEquiv hR hθ hz).symm.toContinuousLinearMap

theorem shiftedCoordinate_eq_inverse {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    shiftedCoordinate hR hθ hz=Ring.inverse (shiftedAugmented hR hθ hz) :=
  (Ring.inverse_unit (shiftedEquiv hR hθ hz).toUnit).symm

theorem compact_shiftedCoordinate_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun p : K×Set.Ici (0:ℝ)=>shiftedCoordinate hR (hpos p.1.property) p.2.property) := by
  simp_rw [shiftedCoordinate_eq_inverse]
  apply continuous_iff_continuousAt.mpr
  intro p
  have hi : ContinuousAt Ring.inverse (shiftedAugmented hR (hpos p.1.property) p.2.property) :=
    NormedRing.inverse_continuousAt (shiftedEquiv hR (hpos p.1.property) p.2.property).toUnit
  exact ContinuousAt.comp (f:=fun q : K×Set.Ici (0:ℝ)=>shiftedAugmented hR (hpos q.1.property) q.2.property)
    (g:=Ring.inverse) hi (compact_shiftedAugmented_continuous hR hK hpos).continuousAt

theorem compact_shiftedCoordinate_uniform_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) {Z : ℝ} (_hZ : 0≤Z) :
    ∃C : ℝ,0<C ∧ ∀(θ : Parameter)(hθ : θ∈K)(z : ℝ)(hz : z∈Set.Icc 0 Z)
      (F : Lp ℝ ∞ (cubeVolume R)),‖shiftedCoordinate hR (hpos hθ) hz.1 F‖≤C*‖F‖ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace (Set.Icc (0:ℝ) Z) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hj : Continuous (fun p : K×Set.Icc (0:ℝ) Z=>
      (p.1,(⟨p.2,p.2.property.1⟩ : Set.Ici (0:ℝ)))) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  obtain ⟨C,hC,hb⟩ := compact_norm_bound ((compact_shiftedCoordinate_continuous hR hK hpos).comp hj)
  refine ⟨C+1,by positivity,?_⟩
  intro θ hθ z hz F
  apply ((shiftedCoordinate hR (hpos hθ) hz.1).le_opNorm F).trans
  exact mul_le_mul_of_nonneg_right ((hb (⟨θ,hθ⟩,⟨z,hz⟩)).trans (by linarith)) (norm_nonneg _)

end
end Resonance.ShiftedParameterContinuity
