import Resonance.PinnedFullAverage
import Resonance.PinnedCompactLocalization
import Resonance.PinnedMaximalDifference

/-! The target-average error is controlled by the original full circle
coarea energy.  All four signs are retained before squaring, and the compact
real graph is returned to that same circle measure by finite winding. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedFullAverageEnergy
noncomputable section
open Resonance.PinnedSmoothing Resonance.PinnedLocalSmooth
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedChartAverage Resonance.PinnedFullAverage
open Resonance.PinnedMeasure Resonance.PinnedCompactGraph
open Resonance.PinnedLegACCircle Resonance.PinnedMaximalDifference

theorem source_average_integrable {H : ℝ×ℝ→ℝ} {x z r κ : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|partialZ H p| ∧ κ≤|partialZ H p-1|)
    {ρ : ℝ→ℝ} (hρ : Continuous ρ)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : MemLp φ 2 circleHaar)
    {a : ℝ} (ha : a∈Metric.ball x (r/4)) (i:Fin 3) :
    IntegrableOn (fun t=>ρ t • periodicLift φ (sourceChart H i (a,t)))
      (Icc (z-r/4) (z+r/4)) :=
  chart_weighted_source_integrable hr (lt_min hκ zero_lt_one)
    (source_charts_regular hκ hs hb i).1 (source_charts_regular hκ hs hb i).2 hρ
    (PinnedPeriodicSourceBounds.circle_L2_lift_locallyIntegrable hφ) ha

theorem full_average_defect_identity {H : ℝ×ℝ→ℝ} {x z r κ : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|partialZ H p| ∧ κ≤|partialZ H p-1|)
    {ρ : ℝ→ℝ} (hρ : Continuous ρ)
    (hρone : (∫t in Icc (z-r/4) (z+r/4),ρ t)=1)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : MemLp φ 2 circleHaar)
    {a : ℝ} (ha : a∈Metric.ball x (r/4)) :
    periodicLift φ a-fullAverage H ρ z r φ a =
      ∫t in Icc (z-r/4) (z+r/4),
        ρ t • (periodicLift φ a+periodicLift φ (H (a,t))-
          periodicLift φ t-periodicLift φ (a+H (a,t)-t)) := by
  have hi (i:Fin 3) := source_average_integrable hr hκ hs hb hρ hφ ha i
  have hsum := integral_sub ((hi 0).add (hi 1)) (hi 2)
  simp only [Pi.add_apply] at hsum
  rw [integral_add (hi 0) (hi 1)] at hsum
  have he := PinnedAverageDefect.source_average_defect_identity (periodicLift φ a)
    hρ.continuousOn.integrableOn_Icc hρone (hi 0) (hi 1) (hi 2)
  have hid : (∫t in Icc (z-r/4) (z+r/4),
      ρ t • (periodicLift φ (sourceChart H 0 (a,t))+
        periodicLift φ (sourceChart H 1 (a,t))-periodicLift φ (sourceChart H 2 (a,t))))
      =fullAverage H ρ z r φ a := by
    simpa only [Complex.real_smul,mul_add,mul_sub,fullAverage,legAverage,
      Pi.add_apply,Pi.sub_apply] using hsum
  rw [hid] at he
  exact he

theorem full_average_point_defect_sq_le {H : ℝ×ℝ→ℝ} {x z r κ : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|partialZ H p| ∧ κ≤|partialZ H p-1|)
    {ρ : ℝ→ℝ} (hρ : Continuous ρ)
    (hρone : (∫t in Icc (z-r/4) (z+r/4),ρ t)=1)
    {B : ℝ} (hB : ∀t∈Icc (z-r/4) (z+r/4),‖ρ t‖≤B)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : MemLp φ 2 circleHaar)
    {a : ℝ} (ha : a∈Metric.ball x (r/4)) :
    ‖periodicLift φ a-fullAverage H ρ z r φ a‖ₑ^2 ≤
      ((ENNReal.ofReal B)^2*volume (Icc (z-r/4) (z+r/4))) *
      (∫⁻t in Icc (z-r/4) (z+r/4),
        ‖periodicLift φ a+periodicLift φ (H (a,t))-
          periodicLift φ t-periodicLift φ (a+H (a,t)-t)‖ₑ^2) := by
  have hi (i:Fin 3) := source_average_integrable hr hκ hs hb hρ hφ ha i
  rw [full_average_defect_identity hr hκ hs hb hρ hρone hφ ha]
  have hF : Integrable (fun t=>ρ t • (periodicLift φ a+
      periodicLift φ (H (a,t))-periodicLift φ t-periodicLift φ (a+H (a,t)-t)))
      (volume.restrict (Icc (z-r/4) (z+r/4))) := by
    simpa only [Complex.real_smul,mul_add,mul_sub,Pi.add_apply,Pi.sub_apply]
      using (((hρ.continuousOn.integrableOn_Icc.smul_const (periodicLift φ a)).add
        (hi 2)).sub (hi 0)).sub (hi 1)
  apply (PinnedAverageDefect.enorm_integral_sq_le _ hF.aestronglyMeasurable).trans
  have he : ∀ᵐt∂volume.restrict (Icc (z-r/4) (z+r/4)),
      ‖ρ t • (periodicLift φ a+periodicLift φ (H (a,t))-
        periodicLift φ t-periodicLift φ (a+H (a,t)-t))‖ₑ^2 ≤
      (ENNReal.ofReal B)^2*‖periodicLift φ a+periodicLift φ (H (a,t))-
        periodicLift φ t-periodicLift φ (a+H (a,t)-t)‖ₑ^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hn := norm_smul_le (ρ t) (periodicLift φ a+periodicLift φ (H (a,t))-
        periodicLift φ t-periodicLift φ (a+H (a,t)-t))
    have hρt := hB t ht
    have he : ‖ρ t • (periodicLift φ a+periodicLift φ (H (a,t))-
        periodicLift φ t-periodicLift φ (a+H (a,t)-t))‖ₑ ≤
      ENNReal.ofReal B*‖periodicLift φ a+periodicLift φ (H (a,t))-
        periodicLift φ t-periodicLift φ (a+H (a,t)-t)‖ₑ := by
      simpa only [ENNReal.ofReal_mul ((norm_nonneg _).trans hρt),ofReal_norm] using
        (ENNReal.ofReal_le_ofReal hn).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hρt (norm_nonneg _)))
    simpa only [mul_pow] using pow_le_pow_left' he 2
  calc
    _ ≤ (∫⁻t in Icc (z-r/4) (z+r/4), (ENNReal.ofReal B)^2*
        ‖periodicLift φ a+periodicLift φ (H (a,t))-
          periodicLift φ t-periodicLift φ (a+H (a,t)-t)‖ₑ^2)*
        (volume.restrict (Icc (z-r/4) (z+r/4))) univ :=
      mul_le_mul_left (lintegral_mono_ae he) _
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      simp only [Measure.restrict_apply_univ]
      ac_rfl

theorem difference_measurable {φ : PinnedPeriodicity.Circle→ℂ}
    (hφ : Measurable φ) : Measurable (difference φ) :=
  (((hφ.comp (circleLeg_continuous 0).measurable).add
    (hφ.comp (circleLeg_continuous 1).measurable)).sub
    (hφ.comp (circleLeg_continuous 2).measurable)).sub
    (hφ.comp (circleLeg_continuous 3).measurable)

theorem difference_quotient (φ : PinnedPeriodicity.Circle→ℂ)
    (k : Ambient) :
    difference φ (quotientCoordinates k)=completeDifference (periodicLift φ) k := by
  simp only [difference,circleLeg_quotient]
  rfl

theorem compact_graph_full_circle_energy_le {d : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (H : ℝ×ℝ→ℝ)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (hH : ContinuousOn H S)
    (hreg : ∀p∈S,graph H p∈regularSurface d) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀φ:PinnedPeriodicity.Circle→ℂ,Measurable φ→
      (∫⁻p in S, ‖periodicLift φ p.1+periodicLift φ (H p)-periodicLift φ p.2-
        periodicLift φ (p.1+H p-p.2)‖ₑ^2) ≤
      C*(∫⁻k,‖difference φ k‖ₑ^2 ∂circleRegularCoarea d) := by
  have hg : ContinuousOn (graph H) S := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3=>ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact continuous_fst.continuousOn
    · exact hH
    · exact continuous_snd.continuousOn
  obtain ⟨C₀,hC₀,hbound⟩ := compact_graph_complete_energy_le hd0 hdU H hS hH hreg
  obtain ⟨C₁,hC₁,hwinding⟩ := PinnedCompactLocalization.compact_periodic_lintegral_le
    hd0 hdU (graph H '' S) (hS.image_of_continuousOn hg)
  refine ⟨C₀*C₁,ENNReal.mul_ne_top hC₀ hC₁,?_⟩
  intro φ hφ
  have hφlift : Measurable (periodicLift φ) :=
    hφ.comp (AddCircle.continuous_mk' period).measurable
  apply (hbound (periodicLift φ) hφlift).trans
  have hh := hwinding (fun k=>‖difference φ k‖ₑ^2) ((difference_measurable hφ).enorm.pow_const 2)
  simp only [difference_quotient] at hh
  simpa only [mul_assoc] using mul_le_mul_right hh C₀

/-- On each closed target subinterval the error of the complete actual
average is bounded by the original full quotient coarea energy.  This is
an extended nonnegative integral statement, so it also covers infinite
collision energy without a default-zero Bochner interpretation. -/
theorem full_average_local_energy_le {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {H : ℝ×ℝ→ℝ} {x z r κ l u : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|partialZ H p| ∧ κ≤|partialZ H p-1|)
    (hreg : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,graph H p∈regularSurface d)
    {ρ : ℝ→ℝ} (hρ : Continuous ρ)
    (hρone : (∫t in Icc (z-r/4) (z+r/4),ρ t)=1)
    (hlu : Icc l u ⊆ Metric.ball x (r/4)) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀φ:PinnedPeriodicity.Circle→ℂ,
      Measurable φ→MemLp φ 2 circleHaar→
      (∫⁻a in Icc l u,‖periodicLift φ a-fullAverage H ρ z r φ a‖ₑ^2) ≤
        C*(∫⁻k,‖difference φ k‖ₑ^2 ∂circleRegularCoarea d) := by
  let I := Icc l u
  let J := Icc (z-r/4) (z+r/4)
  let S := I×ˢJ
  have hJ : J ⊆ Metric.ball z r := by
    dsimp [J]
    rw [←Real.closedBall_eq_Icc]
    exact Metric.closedBall_subset_ball (by linarith)
  have hI : I ⊆ Metric.ball x r :=
    hlu.trans (Metric.ball_subset_ball (by linarith))
  have hS : S ⊆ Metric.ball x r ×ˢ Metric.ball z r := Set.prod_mono hI hJ
  have hSc : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact J).exists_bound_of_continuousOn hρ.continuousOn
  let A := (ENNReal.ofReal B)^2*volume J
  have hA : A≠⊤ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp [J])
  obtain ⟨C,hC,hgraph⟩ := compact_graph_full_circle_energy_le hd0 hdU H hSc
    (hs.continuousOn.mono hS) (fun p hp=>hreg p (hS hp))
  refine ⟨A*C,ENNReal.mul_ne_top hA hC,?_⟩
  intro φ hφ hφL2
  let f := periodicLift φ
  let D : ℝ×ℝ→ℝ≥0∞ := fun p=>‖f p.1+f (H p)-f p.2-f (p.1+H p-p.2)‖ₑ^2
  have hf : Measurable f := hφ.comp (AddCircle.continuous_mk' period).measurable
  have hm : AEMeasurable D (volume.restrict S) := by
    have hH : AEMeasurable H (volume.restrict S) :=
      (hs.continuousOn.mono hS).aemeasurable hSc.measurableSet
    exact ((((hf.comp measurable_fst).aemeasurable.add (hf.comp_aemeasurable hH)).sub
      (hf.comp measurable_snd).aemeasurable).sub
      (hf.comp_aemeasurable ((measurable_fst.aemeasurable.add hH).sub
        measurable_snd.aemeasurable))).enorm.pow_const 2
  have hprod : (∫⁻p in S,D p) = ∫⁻a in I,∫⁻t in J,D (a,t) := by
    have he : (volume.restrict I).prod (volume.restrict J)=volume.restrict S :=
      Measure.prod_restrict I J
    rw [←he]
    exact lintegral_prod D (he.symm ▸ hm)
  calc
    _ ≤ ∫⁻a in I,A*(∫⁻t in J,D (a,t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      exact full_average_point_defect_sq_le hr hκ hs hb hρ hρone hB hφL2 (hlu ha)
    _ = A*(∫⁻p in S,D p) := by
      rw [lintegral_const_mul' _ _ hA,hprod]
    _ ≤ A*(C*(∫⁻k,‖difference φ k‖ₑ^2 ∂circleRegularCoarea d)) :=
      mul_le_mul_right (hgraph φ hφ) A
    _ = _ := by ac_rfl

end
end Resonance.PinnedFullAverageEnergy
