import Resonance.PinnedNearKernelCompactness

/-! Conversion back to the original probability-Haar Hilbert space.
Near-kernel compactness is a conclusion of the actual chart estimates,
not an input to a closed-form or spectral-gap construction. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Resonance.PinnedLpCompactness
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedCircleAE
open Resonance.PinnedClassificationFinal
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem fundamental_square_dominates_circle {φ ψ:PinnedPeriodicity.Circle→ℂ}
    (hφ:Measurable φ) (hψ:Measurable ψ) :
    (∫⁻k,‖φ k-ψ k‖ₑ^2 ∂circleHaar) ≤ (ENNReal.ofReal period)⁻¹*
      (∫⁻x in Icc 0 period,‖periodicLift φ x-periodicLift ψ x‖ₑ^2) := by
  rw [circleHaar,lintegral_smul_measure]
  have he := (AddCircle.measurePreserving_mk period 0).lintegral_comp
    ((hφ.sub hψ).enorm.pow_const 2)
  simp only [zero_add] at he
  rw [←he]
  apply mul_le_mul_right _ ((ENNReal.ofReal period)⁻¹)
  exact lintegral_mono' (Measure.restrict_mono_set volume Ioc_subset_Icc_self) le_rfl

theorem fundamental_pair_energy_cauchy
    {φ:ℕ→PinnedPeriodicity.Circle→ℂ} (hm:∀n,Measurable (φ n))
    (hφ:∀n,MemLp (φ n) 2 circleHaar)
    (henergy:Tendsto (fun p:ℕ×ℕ=>∫⁻x in Icc 0 period,
      ‖periodicLift (φ p.1) x-periodicLift (φ p.2) x‖ₑ^2)
      (atTop×ˢatTop) (𝓝 0)) :
    CauchySeq (fun n=>(hφ n).toLp (φ n)) := by
  have hc : (ENNReal.ofReal period)⁻¹≠⊤ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr period_pos))
  have hscaled := ENNReal.Tendsto.const_mul henergy (Or.inr hc)
  simp only [mul_zero] at hscaled
  have hcircle : Tendsto (fun p:ℕ×ℕ=>∫⁻k,‖φ p.1 k-φ p.2 k‖ₑ^2 ∂circleHaar)
      (atTop×ˢatTop) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled
      (fun _=>zero_le _) (fun p=>fundamental_square_dominates_circle (hm p.1) (hm p.2))
  have hnorm : Tendsto (fun p:ℕ×ℕ=>eLpNorm (fun k=>φ p.1 k-φ p.2 k) 2 circleHaar)
      (atTop×ˢatTop) (𝓝 0) := by
    have he := (ENNReal.continuous_rpow_const (y:=1/(2:ℝ))).continuousAt.tendsto.comp hcircle
    simpa [Function.comp_def,eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠⊤),
      ENNReal.rpow_natCast] using he
  have hreal := (ENNReal.tendsto_toReal_zero_iff
    (fun p:ℕ×ℕ=>((hφ p.1).sub (hφ p.2)).eLpNorm_lt_top.ne)).mpr hnorm
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  rw [←Filter.prod_atTop_atTop_eq]
  convert hreal using 1
  funext p
  rw [Lp.dist_def]
  congr 1
  exact eLpNorm_congr_ae ((hφ p.1).coeFn_toLp.sub (hφ p.2).coeFn_toLp)

/-- Actual full-coarea near-kernel compactness for Borel representatives
of bounded original circle L² data. -/
theorem actual_near_kernel_L2_subsequence {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {φ:ℕ→PinnedPeriodicity.Circle→ℂ} (hm:∀n,Measurable (φ n))
    (hφ:∀n,MemLp (φ n) 2 circleHaar)
    {R:ℝ≥0∞} (hR:R≠⊤) (hbound:∀n,eLpNorm (φ n) 2 circleHaar≤R)
    (henergy:Tendsto (fun n=>∫⁻k,‖PinnedMaximalDifference.difference (φ n) k‖ₑ^2
      ∂circleRegularCoarea d) atTop (𝓝 0)) :
    ∃f:Lp ℂ 2 circleHaar,∃s:ℕ→ℕ,StrictMono s ∧
      Tendsto (fun n=>(hφ (s n)).toLp (φ (s n))) atTop (𝓝 f) := by
  obtain ⟨s,hs,hpair⟩ := PinnedNearKernelCompactness.actual_near_kernel_subsequence_energy
    hd0 hdU hm hφ hR hbound henergy
  obtain ⟨f,hf⟩ := cauchySeq_tendsto_of_complete
    (fundamental_pair_energy_cauchy (fun n=>hm (s n)) (fun n=>hφ (s n)) hpair)
  exact ⟨f,s,hs,hf⟩

end
end Resonance.PinnedLpCompactness
