import Resonance.ShiftedStrongCell

/-! Uniform B_s bounds for the same original resolvent on compact positive
parameter sets. The bounded output is identified with the same physical H_nu
vector, not an independently chosen representative. -/
open MeasureTheory Set
open scoped ENNReal Topology
namespace Resonance.RegularizedCellBounds
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace CollisionFrequency
open ActualPairNormalization PhysicalFiveBasis PhysicalMomentProjection PhysicalWeightedCoercivity
open LinftyPhysicalDomain LinftyFiveAugmentation PositiveLossShift ShiftedAugmentation
open ShiftedParameterContinuity ShiftedStrongCell CompactParameterCell

def boundedOutput {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (1-multiplier hR hθ hz).comp (shiftedCoordinate hR hθ hz)

theorem boundedOutput_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R)) :
    boundedOutput hR hθ hz F=ᵐ[cubeVolume R] (fun k=>z*shiftedCell hR hθ hz F k) :=
  gap_ae hR hθ hz (shiftedCoordinate hR hθ hz F)

theorem boundedOutput_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R)) :
    ‖boundedOutput hR hθ hz F‖≤2*‖shiftedCoordinate hR hθ hz F‖ := by
  change ‖shiftedCoordinate hR hθ hz F-
    multiplier hR hθ hz (shiftedCoordinate hR hθ hz F)‖≤_
  apply (norm_sub_le _ _).trans
  have hb := (multiplier hR hθ hz).le_opNorm (shiftedCoordinate hR hθ hz F)
  have hm := multiplier_bound hR hθ hz
  nlinarith [norm_nonneg (shiftedCoordinate hR hθ hz F)]

theorem compact_shiftedCell_continuous {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    Continuous (fun p : K×Set.Ici (0:ℝ)=>shiftedCell hR (hpos p.1.property) p.2.property) :=
  (compact_shiftedDivide_continuous hR hK hpos).clm_comp
    (compact_shiftedCoordinate_continuous hR hK hpos)

theorem compact_shifted_cell_two_norm_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) {Z : ℝ} (hZ : 0≤Z) :
    ∃C : ℝ,0<C ∧ ∀(θ : Parameter)(hθ : θ∈K)(z : ℝ)(hz : z∈Set.Icc 0 Z)
      (F : Lp ℝ ∞ (cubeVolume R)),
      ‖shiftedCell hR (hpos hθ) hz.1 F‖≤C*‖F‖ ∧
      ‖boundedOutput hR (hpos hθ) hz.1 F‖≤C*‖F‖ ∧
      MemLp (fun k=>referenceFrequency R k*shiftedCell hR (hpos hθ) hz.1 F k) ∞ (cubeVolume R) ∧
      ∀ᵐk∂cubeVolume R,‖referenceFrequency R k*shiftedCell hR (hpos hθ) hz.1 F k‖≤C*‖F‖ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace (Set.Icc (0:ℝ) Z) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hj : Continuous (fun p : K×Set.Icc (0:ℝ) Z=>
      (p.1,(⟨p.2,p.2.property.1⟩ : Set.Ici (0:ℝ)))) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  obtain ⟨M,hM,hm⟩ := compact_norm_bound ((compact_shiftedCell_continuous hR hK hpos).comp hj)
  obtain ⟨B,hB,hb⟩ := compact_shiftedCoordinate_uniform_bound hR hK hpos hZ
  obtain ⟨a,ha,hl⟩ := compact_loss_reference_lower hR hK hpos
  let C := M+2*B+a⁻¹*B+1
  have hC : 0<C := by dsimp [C]; positivity
  have hMC : M≤C := by dsimp [C]; nlinarith [inv_nonneg.mpr ha.le]
  have hBC : 2*B≤C := by dsimp [C]; nlinarith [inv_nonneg.mpr ha.le]
  have haC : a⁻¹*B≤C := by dsimp [C]; nlinarith
  refine ⟨C,hC,?_⟩
  intro θ hθ z hz F
  have hu := shifted_frequency_ae hR (hpos hθ) hz.1 (shiftedCoordinate hR (hpos hθ) hz.1 F)
  have hw : ∀ᵐk∂cubeVolume R,
      ‖referenceFrequency R k*shiftedCell hR (hpos hθ) hz.1 F k‖≤C*‖F‖ := by
    filter_upwards [hu,LinftyRowOperator.ae_norm_bound (shiftedCoordinate hR (hpos hθ) hz.1 F),
      CornerInverseFrequency.referenceFrequency_positive_ae hR,
      loss_positive_ae hR (hpos hθ),ae_restrict_mem (measurable_cube R)] with k hu hv hr hn hk
    change (lossFrequency R (profile θ) k+z)*shiftedCell hR (hpos hθ) hz.1 F k=
      shiftedCoordinate hR (hpos hθ) hz.1 F k at hu
    have hh : referenceFrequency R k≤a⁻¹*(lossFrequency R (profile θ) k+z) := by
      have h := hl θ hθ k hk
      exact ((le_div_iff₀ ha).mpr (by nlinarith [hz.1] : referenceFrequency R k*a≤
        lossFrequency R (profile θ) k+z)).trans_eq (by ring)
    calc
      _ = referenceFrequency R k*‖shiftedCell hR (hpos hθ) hz.1 F k‖ := by
        rw [norm_mul,Real.norm_of_nonneg hr.le]
      _ ≤ a⁻¹*((lossFrequency R (profile θ) k+z)*‖shiftedCell hR (hpos hθ) hz.1 F k‖) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _ = a⁻¹*‖shiftedCoordinate hR (hpos hθ) hz.1 F k‖ := by
        rw [←hu,norm_mul,Real.norm_of_nonneg (add_nonneg hn.le hz.1)]
      _ ≤ a⁻¹*(B*‖F‖) := mul_le_mul_of_nonneg_left (hv.trans (hb θ hθ z hz F)) (inv_nonneg.mpr ha.le)
      _ ≤ C*‖F‖ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right haC (norm_nonneg F)
  refine ⟨?_,?_,?_,hw⟩
  · apply ((shiftedCell hR (hpos hθ) hz.1).le_opNorm F).trans
    exact mul_le_mul_of_nonneg_right ((hm (⟨θ,hθ⟩,⟨z,hz⟩)).trans hMC) (norm_nonneg _)
  · exact (boundedOutput_bound hR (hpos hθ) hz.1 F).trans
      ((mul_le_mul_of_nonneg_left (hb θ hθ z hz F) (by norm_num : (0:ℝ)≤2)).trans
        (by nlinarith [norm_nonneg F]))
  · apply memLp_top_of_bound _ _ hw
    exact ((CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable).mul
      (Lp.stronglyMeasurable (shiftedCell hR (hpos hθ) hz.1 F)).measurable).aestronglyMeasurable

theorem physicalForm_smul_left {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : ℝ) (u v : Space R) :
    physicalForm hR.le hθ (a • u) v=a*physicalForm hR.le hθ u v := by
  simp [physicalForm,map_smul,real_inner_smul_left]

theorem actual_regularized_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (StrongBoundedCell.sourceVector hR F)=0) (v : Space R) :
    s*physicalForm hR.le hθ (s⁻¹ • shiftedCell hR hθ (inv_nonneg.mpr hs.le) F) v+
      (∫k,v k*boundedOutput hR hθ (inv_nonneg.mpr hs.le) F k∂cubeVolume R)=
        ∫k,v k*F k∂cubeVolume R := by
  rw [physicalForm_smul_left hR hθ,←mul_assoc,mul_inv_cancel₀ hs.ne',one_mul]
  exact actual_shifted_cell_pairing hR hθ (inv_nonneg.mpr hs.le) F hQ v

theorem actual_regularized_two_norm_resolvent {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀(θ : Parameter)(hθ : θ∈K)(s : ℝ),1 ≤ s →
      ∀F : Lp ℝ ∞ (cubeVolume R),
      projection hR (hpos hθ) (StrongBoundedCell.sourceVector hR F)=0 →
      ∃u : Space R,∃q : Lp ℝ ∞ (cubeVolume R),
        q=ᵐ[cubeVolume R] u ∧ projection hR (hpos hθ) u=0 ∧
        ‖q‖≤C*‖F‖ ∧ ‖u‖≤(C/s)*‖F‖ ∧
        MemLp (fun k=>referenceFrequency R k*u k) ∞ (cubeVolume R) ∧
        (∀ᵐk∂cubeVolume R,s*‖referenceFrequency R k*u k‖≤C*‖F‖) ∧
        (∀v : Space R,s*physicalForm hR.le (hpos hθ) u v+
          (∫k,v k*q k∂cubeVolume R)=∫k,v k*F k∂cubeVolume R) := by
  obtain ⟨C,hC,hb⟩ := compact_shifted_cell_two_norm_bound hR hK hpos (Z:=1) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro θ hθ s hs F hQ
  have hs0 : 0<s := lt_of_lt_of_le zero_lt_one hs
  have hz0 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0.le
  have hz : s⁻¹∈Set.Icc (0:ℝ) 1 := ⟨hz0,inv_le_one_of_one_le₀ hs⟩
  let w := shiftedCell hR (hpos hθ) hz0 F
  let u : Space R := s⁻¹ • w
  let q := boundedOutput hR (hpos hθ) hz0 F
  have he : (u : E→ℝ)=ᵐ[cubeVolume R] (fun k=>s⁻¹*w k) :=
    (reference_volume_equivalent hR).1.ae_eq (Lp.coeFn_smul s⁻¹ w)
  have hqu : q=ᵐ[cubeVolume R] u := (boundedOutput_ae hR (hpos hθ) hz0 F).trans he.symm
  obtain ⟨hu,hq,hν,hνb⟩ := hb θ hθ s⁻¹ hz F
  have hweight : (fun k=>referenceFrequency R k*u k)=ᵐ[cubeVolume R]
      (fun k=>s⁻¹*(referenceFrequency R k*w k)) := by
    filter_upwards [he] with k hk
    rw [hk]
    ring
  refine ⟨u,q,hqu,?_,hq,?_,?_,?_,?_⟩
  · change projection hR (hpos hθ) (s⁻¹ • w)=0
    rw [map_smul,shifted_cell_micro hR (hpos hθ) hz0 F hQ,smul_zero]
  · change ‖s⁻¹ • w‖≤_
    rw [norm_smul,Real.norm_of_nonneg hz0]
    exact (mul_le_mul_of_nonneg_left hu hz0).trans_eq (by ring)
  · exact (memLp_congr_ae hweight).mpr (hν.const_mul s⁻¹)
  · filter_upwards [hweight,hνb] with k hw hk
    rw [hw,norm_mul,Real.norm_of_nonneg hz0,←mul_assoc,mul_inv_cancel₀ hs0.ne',one_mul]
    exact hk
  · intro v
    exact actual_regularized_pairing hR (hpos hθ) hs0 F hQ v

end
end Resonance.RegularizedCellBounds
