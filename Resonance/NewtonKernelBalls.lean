import Resonance.PolarCoordinates
import Resonance.CornerInverseFrequency

/-! Actual three-dimensional Newton-kernel ball integrals.  These use
the proved Euclidean polar measure, not an assumed HLS estimate. -/
open Real Set MeasureTheory Metric
open scoped ENNReal Topology
namespace Resonance.NewtonKernelBalls
noncomputable section
set_option maxHeartbeats 800000
open Resonance.ResonantMeasure
open Resonance.PolarCoordinates (polarVector polarVector_preserves_volume)

def kernelTwo (x:E) : ℝ≥0∞ := ENNReal.ofReal (‖x‖⁻¹^2)

theorem kernelTwo_measurable : Measurable kernelTwo := by unfold kernelTwo; fun_prop

theorem radial_inverse_square {ρ:ℝ} (_hρ:0<ρ) :
    (∫⁻r:Radius,if (r:ℝ)<ρ then ENNReal.ofReal ((r:ℝ)⁻¹^2) else 0
      ∂Measure.volumeIoiPow 2)=ENNReal.ofReal ρ := by
  have hm : Measurable (fun r:Radius=>if (r:ℝ)<ρ then ENNReal.ofReal ((r:ℝ)⁻¹^2) else 0) := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_subtype_coe measurable_const
    · fun_prop
    · exact measurable_const
  unfold Measure.volumeIoiPow
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm]
  have hp (r:Radius) : ENNReal.ofReal ((r:ℝ)^2)*
      (if (r:ℝ)<ρ then ENNReal.ofReal ((r:ℝ)⁻¹^2) else 0)=
      (if (r:ℝ)<ρ then (1:ℝ≥0∞) else 0) := by
    by_cases hr:(r:ℝ)<ρ
    · rw [if_pos hr,if_pos hr,←ENNReal.ofReal_mul (sq_nonneg _)]
      have hr0 : 0<(r:ℝ) := r.property
      have he : (r:ℝ)^2*(r:ℝ)⁻¹^2=1 := by field_simp [hr0.ne']
      rw [he]
      norm_num
    · simp [hr]
  change (∫⁻r:Radius,ENNReal.ofReal ((r:ℝ)^2)*
      (if (r:ℝ)<ρ then ENNReal.ofReal ((r:ℝ)⁻¹^2) else 0)
      ∂(volume:Measure ℝ).comap Subtype.val)=_
  simp_rw [hp]
  have he := lintegral_subtype_comap (μ:=(volume:Measure ℝ))
    (show MeasurableSet (Ioi (0:ℝ)) from measurableSet_Ioi)
    (fun r:ℝ=>if r<ρ then (1:ℝ≥0∞) else 0)
  rw [he]
  have hi : (∫⁻r in Ioi (0:ℝ),if r<ρ then (1:ℝ≥0∞) else 0)=
      ∫⁻r in Ioo (0:ℝ) ρ,(1:ℝ≥0∞) := by
    rw [←lintegral_indicator measurableSet_Ioo]
    rw [←lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro r
    simp only [indicator_apply,mem_Ioo,mem_Ioi]
    split_ifs <;> simp_all
  rw [hi,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
  simp

theorem kernelTwo_ball_zero {ρ:ℝ} (hρ:0<ρ) :
    (∫⁻x in ball (0:E) ρ,kernelTwo x)=surface univ*ENNReal.ofReal ρ := by
  classical
  let F : E→ℝ≥0∞ := (ball (0:E) ρ).indicator kernelTwo
  have hF : Measurable F := kernelTwo_measurable.indicator measurableSet_ball
  have he := lintegral_map (μ:=surface.prod (Measure.volumeIoiPow 2))
    hF polarVector_preserves_volume.measurable
  rw [polarVector_preserves_volume.map_eq] at he
  rw [←lintegral_indicator measurableSet_ball]
  change (∫⁻x,F x)=_
  rw [he]
  rw [lintegral_prod (fun p:Sphere×Radius=>F (polarVector p))
    (show AEMeasurable (fun p:Sphere×Radius=>F (polarVector p))
      (surface.prod (Measure.volumeIoiPow 2)) from
      (hF.comp polarVector_preserves_volume.measurable).aemeasurable)]
  have hp (p:Sphere×Radius) : F (polarVector p)=
      if (p.2:ℝ)<ρ then ENNReal.ofReal ((p.2:ℝ)⁻¹^2) else 0 := by
    have hnσ : ‖(p.1:E)‖=1 := by simpa only [mem_sphere_zero_iff_norm] using p.1.property
    have hr0 : 0<(p.2:ℝ) := p.2.property
    have hn : ‖polarVector p‖=(p.2:ℝ) := by
      simp only [polarVector,norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hnσ,mul_one]
    change (if polarVector p∈ball (0:E) ρ then kernelTwo (polarVector p) else 0)=_
    simp only [mem_ball_zero_iff,kernelTwo,hn]
  simp_rw [hp]
  simp_rw [radial_inverse_square hρ]
  rw [lintegral_const]
  ring

theorem kernelTwo_ball {ρ:ℝ} (hρ:0<ρ) (k:E) :
    (∫⁻p in ball k ρ,kernelTwo (k-p))=surface univ*ENNReal.ofReal ρ := by
  classical
  rw [←lintegral_indicator measurableSet_ball]
  have he := lintegral_add_left_eq_self (μ:=(volume:Measure E))
    ((ball k ρ).indicator (fun p=>kernelTwo (k-p))) k
  rw [←he]
  have hp (p:E) : (ball k ρ).indicator (fun q=>kernelTwo (k-q)) (k+p)=
      (ball (0:E) ρ).indicator kernelTwo p := by
    have hd : dist (k+p) k=‖p‖ := by rw [dist_eq_norm]; simp
    have hk : kernelTwo (k-(k+p))=kernelTwo p := by simp [kernelTwo]
    change (if k+p∈ball k ρ then kernelTwo (k-(k+p)) else 0)=
      (if p∈ball (0:E) ρ then kernelTwo p else 0)
    simp only [mem_ball,hd,dist_zero_right,hk]
  simp_rw [hp]
  rw [lintegral_indicator measurableSet_ball]
  exact kernelTwo_ball_zero hρ

theorem kernelTwo_radius_bound {ρ:ℝ} (hρ:0<ρ) {x:E} (hx:ρ≤‖x‖) :
    kernelTwo x≤ENNReal.ofReal (ρ⁻¹^2) := by
  have hi : ‖x‖⁻¹≤ρ⁻¹ := inv_anti₀ hρ hx
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg x)) hi 2

/-- A small-volume set has a uniform Newton-square row bound.  Splitting
at the actual ball retains the singular part through the exact polar
integral; the exterior uses the same set's proved volume. -/
theorem kernelTwo_set_bound {ρ C:ℝ} (hρ:0<ρ) (hC:0≤C) (S:Set E)
    (hS:MeasurableSet S) (hvol:volume S≤ENNReal.ofReal (C*ρ^3)) (k:E) :
    (∫⁻p in S,kernelTwo (k-p))≤(surface univ+ENNReal.ofReal C)*ENNReal.ofReal ρ := by
  classical
  let f : E→ℝ≥0∞ := fun p=>kernelTwo (k-p)
  have hf : Measurable f := kernelTwo_measurable.comp (measurable_const.sub measurable_id)
  have hp (p:E) : S.indicator f p≤
      (ball k ρ).indicator f p+S.indicator (fun _=>ENNReal.ofReal (ρ⁻¹^2)) p := by
    by_cases hs:p∈S
    · rw [Set.indicator_of_mem hs,Set.indicator_of_mem hs]
      by_cases hb:p∈ball k ρ
      · rw [Set.indicator_of_mem hb]
        exact le_self_add
      · rw [Set.indicator_of_notMem hb,zero_add]
        apply kernelTwo_radius_bound hρ
        have hh : ρ≤dist p k := le_of_not_gt hb
        simpa only [dist_eq_norm,norm_sub_rev] using hh
    · rw [Set.indicator_of_notMem hs]
      exact zero_le _
  have hI := lintegral_mono (μ:=(volume:Measure E)) hp
  rw [lintegral_indicator hS,lintegral_add_left (hf.indicator measurableSet_ball),
    lintegral_indicator measurableSet_ball,lintegral_indicator hS,lintegral_const,
    Measure.restrict_apply_univ] at hI
  change (∫⁻p in S,kernelTwo (k-p))≤
    (∫⁻p in ball k ρ,kernelTwo (k-p))+ENNReal.ofReal (ρ⁻¹^2)*volume S at hI
  rw [kernelTwo_ball hρ] at hI
  have he : ENNReal.ofReal (ρ⁻¹^2)*ENNReal.ofReal (C*ρ^3)=
      ENNReal.ofReal C*ENNReal.ofReal ρ := by
    rw [←ENNReal.ofReal_mul (sq_nonneg _),←ENNReal.ofReal_mul hC]
    congr 1
    field_simp
  calc
    _ ≤ surface univ*ENNReal.ofReal ρ+ENNReal.ofReal (ρ⁻¹^2)*volume S := hI
    _ ≤ surface univ*ENNReal.ofReal ρ+
        ENNReal.ofReal (ρ⁻¹^2)*ENNReal.ofReal (C*ρ^3) :=
      add_le_add le_rfl (mul_le_mul_right hvol _)
    _ = _ := by rw [he]; ring

end
end Resonance.NewtonKernelBalls
