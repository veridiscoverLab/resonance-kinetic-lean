import Resonance.NewtonLayerEnergy
import Resonance.CornerDepthLipschitz

/-! The full two-variable Newton energy of the actual reference
frequency on the original closed cube.  The proof retains all pairs of
corner layers and the entire compact core. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CornerNewtonEnergy
noncomputable section
set_option maxHeartbeats 1600000
open Resonance.ResonantMeasure Resonance.CollisionFrequency
open Resonance.CornerFrequencyBounds Resonance.CriticalLogShells
open Resonance.CornerInverseFrequency Resonance.CornerLayerVolume
open Resonance.CollisionFrequencyCompactCore Resonance.FiberContinuity
open Resonance.NewtonKernelBalls Resonance.NewtonLayerEnergy

def shellAmplitude (c:ℝ) : ℝ := (c*(Real.exp (-1))^2)⁻¹

theorem shellAmplitude_pos {c:ℝ} (hc:0<c) : 0<shellAmplitude c := by
  unfold shellAmplitude
  positivity

theorem shell_inverse_first {c e v:ℝ} (hc:0<c) (n:ℕ)
    (hel:shellRadius (n+1)<e) (heu:e≤ shellRadius n)
    (hν:c*e^2*(Real.log (1/e))^2≤v) :
    v⁻¹ ≤ shellAmplitude c*(1/((n:ℝ)+8)^2)/(shellRadius n)^2 := by
  have he0 : 0<e := (shellRadius_pos (n+1)).trans hel
  have hq : 0<(n:ℝ)+8 := by positivity
  have hlog : (n:ℝ)+8≤Real.log (1/e) := by
    have hh := Real.log_le_log he0 heu
    rw [shellRadius,Real.log_exp] at hh
    rw [one_div,Real.log_inv]
    linarith
  have hsq : (shellRadius (n+1))^2≤e^2 := by nlinarith [shellRadius_pos (n+1)]
  have hl2 : ((n:ℝ)+8)^2≤(Real.log (1/e))^2 := by nlinarith
  have hlo : c*(shellRadius (n+1))^2*((n:ℝ)+8)^2≤v := by
    apply le_trans _ hν
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsq hc.le) hl2 (sq_nonneg _) (by positivity)
  have hbase : 0<c*(shellRadius (n+1))^2*((n:ℝ)+8)^2 := by
    have hh:=shellRadius_pos (n+1)
    positivity
  apply (inv_anti₀ hbase hlo).trans_eq
  rw [Resonance.CornerDepthLipschitz.shellRadius_add]
  norm_num only [Nat.cast_one]
  unfold shellAmplitude
  field_simp

def cubeFrequency (R:ℝ) : E→ℝ :=
  (cube R).indicator (referenceFrequency R)

def inverseWeight (R:ℝ) (k:E) : ℝ≥0∞ := ENNReal.ofReal ((cubeFrequency R k)⁻¹)

theorem cubeFrequency_measurable {R:ℝ} (hR:0<R) : Measurable (cubeFrequency R) := by
  classical
  exact (referenceFrequency_continuousOn hR.le).measurable_piecewise
    continuousOn_const (cube_isCompact R).measurableSet

theorem inverseWeight_measurable {R:ℝ} (hR:0<R) : Measurable (inverseWeight R) :=
  (cubeFrequency_measurable hR).inv.ennreal_ofReal

theorem inverseWeight_on_cube {R:ℝ} {k:E} (hk:k∈cube R) :
    inverseWeight R k=ENNReal.ofReal ((referenceFrequency R k)⁻¹) := by
  simp only [inverseWeight,cubeFrequency,Set.indicator_of_mem hk]

def layer (R:ℝ) : ℕ→Set E
  | 0 => cube R ∩ (smallLayer (cornerDepth R))ᶜ
  | n+1 => cube R ∩ shell (cornerDepth R) n

def radius : ℕ→ℝ
  | 0 => 1
  | n+1 => shellRadius n

def coefficient : ℕ→ℝ
  | 0 => 1
  | n+1 => 1/((n:ℝ)+8)^2

theorem smallLayer_measurable (R:ℝ) : MeasurableSet (smallLayer (cornerDepth R)) :=
  (measurableSet_lt measurable_const (cornerDepth_continuous R).measurable).inter
    (measurableSet_le (cornerDepth_continuous R).measurable measurable_const)

theorem layer_measurable (R:ℝ) (n:ℕ) : MeasurableSet (layer R n) := by
  cases n with
  | zero => exact (cube_isCompact R).measurableSet.inter (smallLayer_measurable R).compl
  | succ n =>
    exact (cube_isCompact R).measurableSet.inter
      ((measurableSet_lt measurable_const (cornerDepth_continuous R).measurable).inter
        (measurableSet_le (cornerDepth_continuous R).measurable measurable_const))

theorem layer_union (R:ℝ) : (⋃n:ℕ,layer R n)=cube R := by
  ext k
  constructor
  · intro hk
    obtain ⟨n,hn⟩:=mem_iUnion.mp hk
    cases n <;> exact hn.1
  · intro hk
    by_cases hs:k∈smallLayer (cornerDepth R)
    · rw [smallLayer_eq_union] at hs
      obtain ⟨n,hn⟩:=mem_iUnion.mp hs
      exact mem_iUnion.mpr ⟨n+1,hk,hn⟩
    · exact mem_iUnion.mpr ⟨0,hk,hs⟩

theorem radius_pos (n:ℕ) : 0<radius n := by
  cases n with
  | zero => norm_num [radius]
  | succ n => exact shellRadius_pos n

theorem coefficient_nonnegative (n:ℕ) : 0≤coefficient n := by
  cases n <;> simp only [coefficient] <;> positivity

theorem coefficient_summable : Summable coefficient := by
  apply (summable_nat_add_iff 1).mp
  have h := (Real.summable_one_div_nat_add_rpow 8 2).mpr (by norm_num)
  have he (n:ℕ) : |(n:ℝ)+8|=(n:ℝ)+8 := abs_of_nonneg (by positivity)
  simpa only [coefficient,he,Real.rpow_ofNat] using h

theorem layer_volume_bounds {R:ℝ} (hR:0<R) :
    ∃C:ℝ,0≤C ∧ ∀n,volume (layer R n)≤ENNReal.ofReal (C*(radius n)^3) := by
  let C : ℝ := (volume (cube R)).toReal+8*(2*R)^3
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hcv : (volume (cube R)).toReal≤C := by
    dsimp [C]
    have hh : 0≤8*(2*R)^3 := by positivity
    linarith
  have hscale : 8*(2*R)^3≤C := by
    dsimp [C]
    linarith [ENNReal.toReal_nonneg (a:=volume (cube R))]
  refine ⟨C,hC0,?_⟩
  intro n
  cases n with
  | zero =>
    simp only [radius,one_pow,mul_one]
    apply (measure_mono inter_subset_left).trans
    rw [←ENNReal.ofReal_toReal (cube_isCompact R).measure_lt_top.ne]
    exact ENNReal.ofReal_le_ofReal hcv
  | succ n =>
    have hsub : layer R (n+1)⊆{k∈cube R|cornerDepth R k≤ shellRadius n} :=
      fun k hk=>⟨hk.1,hk.2.2⟩
    apply ((measure_mono hsub).trans (cornerDepth_layer_volume_le hR _)).trans
    have he : 8*(ENNReal.ofReal (2*R*shellRadius n))^3=
        ENNReal.ofReal ((8*(2*R)^3)*(shellRadius n)^3) := by
      rw [←ENNReal.ofReal_pow (by have hh:=shellRadius_pos n; positivity),
        show (8:ℝ≥0∞)=ENNReal.ofReal (8:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤8)]
      congr 1
      ring
    rw [he]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hscale (by have hh:=shellRadius_pos n; positivity))

theorem layer_weight_bounds {R:ℝ} (hR:0<R) :
    ∃A:ℝ,0≤A ∧ ∀n k,k∈layer R n→
      inverseWeight R k≤ENNReal.ofReal (A*coefficient n/(radius n)^2) := by
  obtain ⟨m,hm,hcore⟩ := referenceFrequency_compactCore_lower hR
    (show 0<2*R*Real.exp (-8) by positivity)
  let A : ℝ := m⁻¹+shellAmplitude (referenceLower R)
  have hamp:=shellAmplitude_pos (referenceLower_pos hR)
  have hA:0≤A := by dsimp [A]; positivity
  have hmA:m⁻¹≤A := by dsimp [A]; linarith
  have hsA:shellAmplitude (referenceLower R)≤A := by
    dsimp [A]
    have hh : 0 < m⁻¹ := inv_pos.mpr hm
    linarith
  refine ⟨A,hA,?_⟩
  intro n k hk
  cases n with
  | zero =>
    rw [inverseWeight_on_cube hk.1]
    simp only [coefficient,radius,one_pow,mul_one,div_one]
    by_cases he:0<cornerDepth R k
    · have he1 : Real.exp (-8)<cornerDepth R k := by
        by_contra h
        exact hk.2 ⟨he,le_of_not_gt h⟩
      have hr : 2*R*Real.exp (-8)≤cornerRadius R k := by
        rw [cornerDepth_eq_radius_div hR] at he1
        exact (show 2*R*Real.exp (-8)=Real.exp (-8)*(2*R) by ring).le.trans
          ((le_div_iff₀ (by positivity)).mp he1.le)
      exact ENNReal.ofReal_le_ofReal ((inv_anti₀ hm (hcore k hk.1 hr)).trans hmA)
    · rw [referenceFrequency_corner_zero (corner_of_nonpositive_depth hR hk.1 (le_of_not_gt he))]
      simp
  | succ n =>
    rw [inverseWeight_on_cube hk.1]
    have hsmall : 0<cornerDepth R k ∧ cornerDepth R k≤Real.exp (-8) :=
      ⟨(shellRadius_pos (n+1)).trans hk.2.1,hk.2.2.trans (shellRadius_le_cutoff n)⟩
    have hv := (referenceFrequency_corner_scale hR hk.1 hsmall.1
      (hsmall.2.trans exp_cutoff_le)).1
    apply ENNReal.ofReal_le_ofReal
    apply (shell_inverse_first (referenceLower_pos hR) n hk.2.1 hk.2.2 hv).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsA (by positivity)) (sq_nonneg _)

theorem reference_newton_pair_finite {R:ℝ} (hR:0<R) :
    pairEnergy (inverseWeight R) (cube R) (cube R)<∞ := by
  obtain ⟨C,hC,hV⟩:=layer_volume_bounds hR
  obtain ⟨A,hA,hW⟩:=layer_weight_bounds hR
  have h := union_energy_finite (inverseWeight_measurable hR) (layer R)
    (layer_measurable R) radius coefficient radius_pos coefficient_nonnegative
    coefficient_summable hC hA hV hW
  rwa [layer_union] at h

/-- The requested full joint integral, with the literal reference
frequency and the same original cube volume in both variables.  The
zero-at-corner real inverse is used only on a previously proved null
set; no diagonal or corner region is removed from the integral. -/
theorem reference_newton_energy_finite {R:ℝ} (hR:0<R) :
    (∫⁻p:E×E,
      ENNReal.ofReal ((referenceFrequency R p.1)⁻¹)*
      ENNReal.ofReal ((referenceFrequency R p.2)⁻¹)*kernelTwo (p.2-p.1)
      ∂((volume:Measure E).restrict (cube R)).prod (volume.restrict (cube R)))<∞ := by
  let μ : Measure E := volume.restrict (cube R)
  have hm : Measurable (fun p:E×E=>inverseWeight R p.1*inverseWeight R p.2*kernelTwo (p.1-p.2)) :=
    (((inverseWeight_measurable hR).comp measurable_fst).mul
      ((inverseWeight_measurable hR).comp measurable_snd)).mul
        (kernelTwo_measurable.comp (measurable_fst.sub measurable_snd))
  have hc : ∀ᵐp:E×E∂μ.prod μ,p.1∈cube R ∧ p.2∈cube R := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem ((cube_isCompact R).measurableSet.prod (cube_isCompact R).measurableSet)
  have he : (∫⁻p:E×E,
      ENNReal.ofReal ((referenceFrequency R p.1)⁻¹)*
      ENNReal.ofReal ((referenceFrequency R p.2)⁻¹)*kernelTwo (p.2-p.1) ∂μ.prod μ)=
      pairEnergy (inverseWeight R) (cube R) (cube R) := by
    calc
      _ = ∫⁻p:E×E,inverseWeight R p.1*inverseWeight R p.2*kernelTwo (p.1-p.2) ∂μ.prod μ := by
        apply lintegral_congr_ae
        filter_upwards [hc] with p hp
        rw [inverseWeight_on_cube hp.1,inverseWeight_on_cube hp.2]
        simp only [kernelTwo,norm_sub_rev]
      _ = _ := lintegral_prod _ hm.aemeasurable
  change (∫⁻p:E×E,
      ENNReal.ofReal ((referenceFrequency R p.1)⁻¹)*
      ENNReal.ofReal ((referenceFrequency R p.2)⁻¹)*kernelTwo (p.2-p.1) ∂μ.prod μ)<∞
  rw [he]
  exact reference_newton_pair_finite hR

end
end Resonance.CornerNewtonEnergy
