import Resonance.CrossRowPointwise
import Resonance.FrequencyWeightedKernel

/-! The real moving-plane integral is identified with the exact
incoming--outgoing density, with integrability proved before converting
the nonnegative integral.  The actual RJ weight is then instantiated
using a genuine continuous extension that agrees on every sharp flag. -/
open Real Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Resonance.CrossDensityContinuity
noncomputable section
set_option maxHeartbeats 1200000
open Resonance.ResonantMeasure
open Resonance.PlaneCoarea (E2)
open Resonance.CrossPairCoordinates Resonance.CrossRowPointwise
open Resonance.FiberContinuity

theorem sharp_ofReal (R:ℝ) (Φ:FourMomenta→ℝ) (q:FourMomenta) :
    (CoareaNormalization.allFourFlags R).indicator (fun q=>ENNReal.ofReal (Φ q)) q=
      ENNReal.ofReal (CoareaNormalization.sharpReadout R Φ q) := by
  by_cases hq:q∈CoareaNormalization.allFourFlags R
  · simp [CoareaNormalization.sharpReadout,Set.indicator_of_mem hq]
  · simp [CoareaNormalization.sharpReadout,Set.indicator_of_notMem hq]

theorem sharp_nonnegative {R:ℝ} {Φ:FourMomenta→ℝ}
    (hΦ:∀q∈CoareaNormalization.allFourFlags R,0≤Φ q) (q:FourMomenta) :
    0≤CoareaNormalization.sharpReadout R Φ q := by
  by_cases hq:q∈CoareaNormalization.allFourFlags R
  · rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem hq]
    exact hΦ q hq
  · simp [CoareaNormalization.sharpReadout,Set.indicator_of_notMem hq]

theorem planeRow_nonnegative {R:ℝ} {Φ:FourMomenta→ℝ}
    (hΦ:∀q∈CoareaNormalization.allFourFlags R,0≤Φ q) (k p:E) :
    0≤planeRow R Φ k p := by
  unfold planeRow planeIntegral
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (integral_nonneg (fun z=>sharp_nonnegative hΦ _))

theorem density_eq_ofReal_planeRow {R:ℝ} (hR:0≤R)
    (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ)
    (hpos:∀q∈CoareaNormalization.allFourFlags R,0≤Φ q) (k p:E) :
    CrossPairDensity.density R (fun q=>ENNReal.ofReal (Φ q)) (k,p)=
      ENNReal.ofReal (planeRow R Φ k p) := by
  let g:E2→ℝ := fun z=>CoareaNormalization.sharpReadout R Φ (crossQuartet ((k,p),z))
  have hm:Measurable g := (CoareaNormalization.sharpReadout_measurable R hΦ.measurable).comp
    (crossQuartet_measurable.comp (measurable_const.prodMk measurable_id))
  obtain ⟨B,hB,hbound⟩:=PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  have hi:Integrable g (finitePlaneMeasure R) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (ae_of_all _ (crossSharp_bound hB Φ hbound k p))
  have hgpos:∀z,0≤g z := fun z=>sharp_nonnegative hpos _
  have he : (∫⁻z:E2,ENNReal.ofReal (g z))=
      ∫⁻z:E2,ENNReal.ofReal (g z) ∂finitePlaneMeasure R := by
    symm
    rw [finitePlaneMeasure,←lintegral_indicator measurableSet_closedBall]
    apply lintegral_congr
    intro z
    by_cases hz:z∈closedBall (0:E2) (6*R)
    · exact Set.indicator_of_mem hz _
    · have hzero:g z=0 :=
        Set.indicator_of_notMem (fun h=>hz (crossQuartet_source_bound hR k p h)) Φ
      rw [Set.indicator_of_notMem hz,hzero,ENNReal.ofReal_zero]
  have hpref : (1/2:ℝ≥0∞)*ENNReal.ofReal (‖p-k‖⁻¹)=ENNReal.ofReal ((2*‖p-k‖)⁻¹) := by
    rw [mul_inv_rev,ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _)),
      ENNReal.ofReal_inv_of_pos (by norm_num:(0:ℝ)<2)]
    norm_num only [ENNReal.ofReal_ofNat]
    simp only [one_div]
    exact mul_comm _ _
  unfold CrossPairDensity.density
  simp_rw [sharp_ofReal]
  change (1/2:ℝ≥0∞)*ENNReal.ofReal (‖p-k‖⁻¹)*(∫⁻z:E2,ENNReal.ofReal (g z))=_
  rw [he,←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hgpos),hpref,
    ←ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity))]
  congr 1
  rw [planeRow,planeIntegral_box hR]

theorem density_toReal_planeRow {R:ℝ} (hR:0≤R)
    (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ)
    (hpos:∀q∈CoareaNormalization.allFourFlags R,0≤Φ q) (k p:E) :
    (CrossPairDensity.density R (fun q=>ENNReal.ofReal (Φ q)) (k,p)).toReal=
      planeRow R Φ k p := by
  rw [density_eq_ofReal_planeRow hR Φ hΦ hpos,ENNReal.toReal_ofReal (planeRow_nonnegative hpos k p)]

theorem density_congr_on_flags (R:ℝ) (w v:FourMomenta→ℝ≥0∞)
    (hwv:∀q∈CoareaNormalization.allFourFlags R,w q=v q) (p:E×E) :
    CrossPairDensity.density R w p=CrossPairDensity.density R v p := by
  unfold CrossPairDensity.density
  congr 1
  apply lintegral_congr
  intro z
  by_cases hq:crossQuartet (p,z)∈CoareaNormalization.allFourFlags R
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq]
    exact hwv _ hq
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq]

theorem actual_weight_extension {R:ℝ} {θ:Thermodynamics.Parameter}
    (hθ:θ∈Thermodynamics.positiveDomain R) :
    ∃Φ:FourMomenta→ℝ,Continuous Φ ∧
      (∀q∈CoareaNormalization.allFourFlags R,0≤Φ q) ∧
      (∀q∈CoareaNormalization.allFourFlags R,WeightedJointMeasure.weight θ q=ENNReal.ofReal (Φ q)) := by
  let f:C(cube R,ℝ):=⟨fun k=>WeightedJointMeasure.profile θ k,
    continuousOn_iff_continuous_restrict.mp (FrequencyWeightedKernel.profile_continuousOn hθ)⟩
  let g:C(E,ℝ):=continuousExtension R f
  let Φ:FourMomenta→ℝ:=fun q=>∏i:Fin 4,g (q i)
  have hg:∀k∈cube R,g k=WeightedJointMeasure.profile θ k :=
    fun k hk=>continuousExtension_eq R f ⟨k,hk⟩
  have hΦ:Continuous Φ := by
    apply continuous_finset_prod
    intro i _
    exact g.continuous.comp (continuous_apply i)
  have he:∀q∈CoareaNormalization.allFourFlags R,Φ q=∏i:Fin 4,WeightedJointMeasure.profile θ (q i) := by
    intro q hq
    exact Finset.prod_congr rfl (fun i _=>hg (q i) (hq i))
  refine ⟨Φ,hΦ,?_,?_⟩
  · intro q hq
    rw [he q hq]
    exact Finset.prod_nonneg (fun i _=>(WeightedJointMeasure.profile_pos hθ (hq i)).le)
  · intro q hq
    rw [he q hq]
    rfl

/-- Actual RJ kernel, full four flags, original output cube including
its boundary.  The input exceptional set is proved volume-null. -/
theorem actual_cross_density_continuousWithinAt_ae {R:ℝ} (hR:0≤R)
    {θ:Thermodynamics.Parameter} (hθ:θ∈Thermodynamics.positiveDomain R)
    {k:E} (hk:k∈cube R) :
    ∀ᵐp:E∂volume,ContinuousWithinAt
      (fun a:E=>(CrossPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal)
      (cube R) k := by
  obtain ⟨Φ,hΦ,hpos,he⟩:=actual_weight_extension hθ
  have hrow (a p:E) : (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (a,p)).toReal=
      planeRow R Φ a p := by
    rw [density_congr_on_flags R _ _ he,density_toReal_planeRow hR Φ hΦ hpos]
  simp_rw [hrow]
  exact planeRow_continuousWithinAt_ae hR Φ hΦ hk

end
end Resonance.CrossDensityContinuity
