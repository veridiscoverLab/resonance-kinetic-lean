import Resonance.NewtonPotentialTails

/-! A uniform, quantitative Newton-row tail for the actual reference
frequency.  All input corner layers act on the same arbitrary output
point; no output-dependent exceptional set is introduced. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CornerNewtonTail
noncomputable section
set_option maxHeartbeats 1600000
open Resonance.ResonantMeasure Resonance.CollisionFrequency
open Resonance.CornerFrequencyBounds Resonance.CriticalLogShells
open Resonance.CornerInverseFrequency Resonance.CornerDepthLipschitz
open Resonance.NewtonLayerEnergy Resonance.NewtonPotentialTails
open Resonance.CornerNewtonEnergy Resonance.FiberContinuity

def positiveTail (R η:ℝ) : Set E := {p∈cube R|0<cornerDepth R p ∧ cornerDepth R p≤η}
def fullTail (R η:ℝ) : Set E := {p∈cube R|cornerDepth R p≤η}

theorem positiveTail_measurable (R η:ℝ) : MeasurableSet (positiveTail R η) :=
  (cube_isCompact R).measurableSet.inter
    ((measurableSet_lt measurable_const (cornerDepth_continuous R).measurable).inter
      (measurableSet_le (cornerDepth_continuous R).measurable measurable_const))

theorem fullTail_measurable (R η:ℝ) : MeasurableSet (fullTail R η) :=
  (cube_isCompact R).measurableSet.inter
    (measurableSet_le (cornerDepth_continuous R).measurable measurable_const)

theorem positiveTail_shell_union (R:ℝ) (N:ℕ) :
    positiveTail R (shellRadius N)=⋃j:ℕ,layer R (N+j+1) := by
  ext p
  constructor
  · intro hp
    obtain ⟨n,hnlo,hnhi⟩ := scalar_shell_cover hp.2.1
      (hp.2.2.trans (shellRadius_le_cutoff N))
    have hN : N≤n := by
      by_contra hh
      have hlt:n<N := Nat.lt_of_not_ge hh
      have hrad:=shellRadius_antitone (Nat.succ_le_of_lt hlt)
      exact (not_lt_of_ge hp.2.2) (hrad.trans_lt hnlo)
    refine mem_iUnion.mpr ⟨n-N,?_⟩
    rw [Nat.add_sub_of_le hN]
    exact ⟨hp.1,hnlo,hnhi⟩
  · intro hp
    obtain ⟨j,hj⟩:=mem_iUnion.mp hp
    exact ⟨hj.1,(shellRadius_pos (N+j+1)).trans hj.2.1,
      hj.2.2.trans (shellRadius_antitone (Nat.le_add_right N j))⟩

theorem fullTail_integral_eq_positive {R:ℝ} (hR:0<R) (η:ℝ) (k:E) :
    (∫⁻p in fullTail R η,inverseWeight R p*(1+kernelOne (k-p)))=
    ∫⁻p in positiveTail R η,inverseWeight R p*(1+kernelOne (k-p)) := by
  classical
  rw [←lintegral_indicator (fullTail_measurable R η),
    ←lintegral_indicator (positiveTail_measurable R η)]
  apply lintegral_congr
  intro p
  by_cases hp:p∈fullTail R η
  · rw [Set.indicator_of_mem hp]
    by_cases he:0<cornerDepth R p
    · rw [Set.indicator_of_mem (show p∈positiveTail R η from ⟨hp.1,he,hp.2⟩)]
    · have hz:inverseWeight R p=0 := by
        rw [inverseWeight_on_cube hp.1,
          referenceFrequency_corner_zero (corner_of_nonpositive_depth hR hp.1 (le_of_not_gt he))]
        simp
      rw [hz,zero_mul,Set.indicator_of_notMem (show p∉positiveTail R η from fun h=>he h.2.1)]
  · rw [Set.indicator_of_notMem hp,
      Set.indicator_of_notMem (show p∉positiveTail R η from fun h=>hp ⟨h.1,h.2.2⟩)]

theorem shell_row_bounds {R:ℝ} (hR:0<R) :
    ∃K:ℝ,0≤K ∧ ∀n:ℕ,∀k:E,
      (∫⁻p in layer R (n+1),inverseWeight R p*(1+kernelOne (k-p)))≤
        ENNReal.ofReal (K/((n:ℝ)+8)^2) := by
  obtain ⟨C,hC,hV⟩:=layer_volume_bounds hR
  obtain ⟨A,hA,hW⟩:=layer_weight_bounds hR
  let K:ℝ:=A*(sphereArea+2*C)
  have ha:=sphereArea_nonnegative
  have hK:0≤K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro n k
  have hr:=shellRadius_pos n
  have hr1:shellRadius n≤1 := (shellRadius_le_cutoff n).trans (by
    rw [←Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num))
  have hbound:=one_add_kernelOne_set_bound hr hr1 hC (layer R (n+1))
    (layer_measurable R (n+1)) (hV (n+1)) k
  calc
    _ ≤ ∫⁻p in layer R (n+1),
        ENNReal.ofReal (A*(1/((n:ℝ)+8)^2)/(shellRadius n)^2)*(1+kernelOne (k-p)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (layer_measurable R (n+1))] with p hp
      exact mul_le_mul_left (hW (n+1) p hp) _
    _ = ENNReal.ofReal (A*(1/((n:ℝ)+8)^2)/(shellRadius n)^2)*
        (∫⁻p in layer R (n+1),1+kernelOne (k-p)) := by
      exact lintegral_const_mul _ (show Measurable (fun p:E=>1+kernelOne (k-p)) from
        measurable_const.add (kernelOne_measurable.comp (measurable_const.sub measurable_id)))
    _ ≤ ENNReal.ofReal (A*(1/((n:ℝ)+8)^2)/(shellRadius n)^2)*
        ENNReal.ofReal ((sphereArea+2*C)*(shellRadius n)^2) := mul_le_mul_right hbound _
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [K]
      field_simp

theorem exponential_tail_bound {R:ℝ} (hR:0<R) :
    ∃K:ℝ,0≤K ∧ ∀N:ℕ,∀k:E,
      (∫⁻p in fullTail R (shellRadius N),inverseWeight R p*(1+kernelOne (k-p)))≤
        ENNReal.ofReal (K/((N:ℝ)+7)) := by
  obtain ⟨K,hK,hrow⟩:=shell_row_bounds hR
  refine ⟨K,hK,?_⟩
  intro N k
  rw [fullTail_integral_eq_positive hR,positiveTail_shell_union]
  apply (lintegral_iUnion_le _ _).trans
  calc
    _ ≤ ∑'j:ℕ,ENNReal.ofReal (K/(((N+j:ℕ):ℝ)+8)^2) := ENNReal.tsum_le_tsum (fun j=>hrow (N+j) k)
    _ = ENNReal.ofReal K*∑'j:ℕ,ENNReal.ofReal (1/(((N+j:ℕ):ℝ)+8)^2) := by
      have hp (j:ℕ) : ENNReal.ofReal (K/(((N+j:ℕ):ℝ)+8)^2)=
          ENNReal.ofReal K*ENNReal.ofReal (1/(((N+j:ℕ):ℝ)+8)^2) := by
        rw [←ENNReal.ofReal_mul hK]
        congr 1
        ring
      simp_rw [hp]
      exact ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal (1/((N:ℝ)+7)) :=
      mul_le_mul_right (inverse_square_tail_bound N) _
    _ = _ := by rw [←ENNReal.ofReal_mul hK]; congr 1; ring

/-- Uniform in every output point, including every corner, for the
same full input corner layer and the literal reference frequency. -/
theorem reference_newton_tail {R:ℝ} (hR:0<R) :
    ∃C:ℝ,0≤C ∧ ∀η:ℝ,0<η→η≤Real.exp (-8)→∀k:E,
      (∫⁻p in fullTail R η,ENNReal.ofReal ((referenceFrequency R p)⁻¹)*
        (1+kernelOne (k-p)))≤ENNReal.ofReal (C/Real.log (1/η)) := by
  obtain ⟨K,hK,hbound⟩:=exponential_tail_bound hR
  refine ⟨2*K,by positivity,?_⟩
  intro η hη hηsmall k
  obtain ⟨N,hlo,hhi⟩:=scalar_shell_cover hη hηsmall
  have hLpos:0<Real.log (1/η) := by
    have hh:=Real.log_le_log hη hηsmall
    rw [Real.log_exp] at hh
    rw [one_div,Real.log_inv]
    linarith
  have hL:Real.log (1/η)≤2*((N:ℝ)+7) := by
    have hh:=Real.log_le_log (shellRadius_pos (N+1)) hlo.le
    rw [shellRadius,Real.log_exp] at hh
    norm_num only [Nat.cast_add,Nat.cast_one] at hh
    rw [one_div,Real.log_inv]
    have hN:(0:ℝ)≤N := Nat.cast_nonneg N
    linarith
  calc
    _ = ∫⁻p in fullTail R η,inverseWeight R p*(1+kernelOne (k-p)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (fullTail_measurable R η)] with p hp
      rw [inverseWeight_on_cube hp.1]
    _ ≤ ∫⁻p in fullTail R (shellRadius N),inverseWeight R p*(1+kernelOne (k-p)) :=
      lintegral_mono_set (fun p hp=>⟨hp.1,hp.2.trans hhi⟩)
    _ ≤ ENNReal.ofReal (K/((N:ℝ)+7)) := hbound N k
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_div_iff₀ (show 0<(N:ℝ)+7 by positivity) hLpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hL hK]

end
end Resonance.CornerNewtonTail
