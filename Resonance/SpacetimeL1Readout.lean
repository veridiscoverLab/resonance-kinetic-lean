import Resonance.SpacetimeDifferenceSlices
import Resonance.SpacetimeFullRecovery
import Resonance.ReferenceMomentFunctionals

/-! The strong weighted source controls the literal L²(time,space;L¹(cube))
reading. Inverse reference-frequency integrability is proved for the original
cube, including its retained zero-frequency corners. No unweighted L² claim
is substituted for this reading. -/
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace Resonance.SpacetimeL1Readout
noncomputable section
open ResonantMeasure ActualPairNormalization ReferenceMomentFunctionals
open SpacetimePairing SpacetimeReference ProductL2Slices

theorem original_slices_integrable {R : ℝ} (hR : 0 < R) (T : ℝ) (u : Space R T) :
    ∀ᵐ a ∂baseMeasure T, Integrable (fun k => u (a,k)) (cubeVolume R) := by
  letI := SpacetimeReference.reference_finite hR.le
  filter_upwards [slice_ae u] with a ha
  exact (unweighted_integrable hR (slice u a)).congr
    ((ReferenceFrequencySpace.reference_volume_equivalent hR).1.ae_eq ha)

theorem cube_integral_abs_bound {R : ℝ} (hR : 0 < R)
    (u : ReferenceFrequencySpace.Space R) :
    (∫ k, |u k| ∂cubeVolume R) ≤ ‖inverseVector hR‖ * ‖u‖ := by
  let v : ReferenceFrequencySpace.Space R := (Lp.memLp u).norm.toLp _
  have hv : (v : E → ℝ) =ᵐ[ReferenceFrequencySpace.referenceMeasure R] (fun k => ‖u k‖) :=
    (Lp.memLp u).norm.coeFn_toLp
  have hn : ‖v‖ ≤ ‖u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hv] with k hk
    rw [hk,norm_norm]
  calc
    _ = ∫ k, v k ∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [(ReferenceFrequencySpace.reference_volume_equivalent hR).1.ae_eq hv]
        with k hk
      simpa only [Real.norm_eq_abs] using hk.symm
    _ = inner ℝ (inverseVector hR) v := integral_as_inner hR v
    _ ≤ ‖inverseVector hR‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (norm_nonneg _)

theorem full_L2_L1_bound {R : ℝ} (hR : 0 < R) (T : ℝ) (u : Space R T) :
    (∫⁻ a, ENNReal.ofReal ((∫ k, |u (a,k)| ∂cubeVolume R)^2) ∂baseMeasure T) ≤
      ENNReal.ofReal (‖inverseVector hR‖^2) * ENNReal.ofReal (‖u‖^2) := by
  letI := SpacetimeReference.reference_finite hR.le
  have hpoint : ∀ᵐ a ∂baseMeasure T,
      (∫ k, |u (a,k)| ∂cubeVolume R)^2 ≤ ‖inverseVector hR‖^2 * ‖slice u a‖^2 := by
    filter_upwards [slice_ae u] with a ha
    have he : (∫ k, |u (a,k)| ∂cubeVolume R) = ∫ k, |slice u a k| ∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [(ReferenceFrequencySpace.reference_volume_equivalent hR).1.ae_eq ha]
        with k hk
      exact congrArg abs hk.symm
    rw [he]
    have h := cube_integral_abs_bound hR (slice u a)
    have h0 : 0 ≤ ∫ k, |slice u a k| ∂cubeVolume R := integral_nonneg (fun _ => abs_nonneg _)
    nlinarith [sq_nonneg (‖inverseVector hR‖ * ‖slice u a‖ - ∫ k, |slice u a k| ∂cubeVolume R)]
  erw [SpacetimeFullRecovery.norm_square_lintegral_slices u]
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hpoint] with a ha
  rw [←ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ha

theorem strong_L2_L1_readout {R : ℝ} (hR : 0 < R) (T : ℝ)
    {ι : Type*} {l : Filter ι} {v : ι → Space R T} {u : Space R T}
    (hv : Tendsto v l (𝓝 u)) :
    Tendsto (fun n => ∫⁻ a, ENNReal.ofReal
      ((∫ k, |(v n-u) (a,k)| ∂cubeVolume R)^2) ∂baseMeasure T) l (𝓝 0) := by
  have hn : Tendsto (fun n => ‖v n-u‖^2) l (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by norm_num : 2≠0)] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hn
  have hb := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal (‖inverseVector hR‖^2)) he (Or.inr ENNReal.ofReal_ne_top)
  have hb0 : Tendsto (fun n => ENNReal.ofReal (‖inverseVector hR‖^2) *
      ENNReal.ofReal (‖v n-u‖^2)) l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero,mul_zero] using hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb0
    (fun _ => zero_le _) (fun n => full_L2_L1_bound hR T (v n-u))

end
end Resonance.SpacetimeL1Readout
