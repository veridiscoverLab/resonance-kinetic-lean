import Resonance.PinnedLpCompactness

/-! The final compactness statement uses arbitrary elements of the original
probability-Haar L² space and the full Euclidean-normalized coarea, with the
same positive quartet weight as the maximal closed difference operator.
Completed representatives are transferred by the proved all-four-leg AC. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Resonance.PinnedWeightedCompactness
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedMeasureNormalization Resonance.PinnedLegACCircle
open Resonance.PinnedMaximalDifference
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem unweighted_difference_energy_ae_eq {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {φ ψ:PinnedPeriodicity.Circle→ℂ} (he:φ=ᵐ[circleHaar]ψ) :
    (∫⁻k,‖difference φ k‖ₑ^2 ∂circleRegularCoarea d)=
      ∫⁻k,‖difference ψ k‖ₑ^2 ∂circleRegularCoarea d := by
  apply lintegral_congr_ae
  apply (circle_coarea_ae_iff d _).mp
  filter_upwards [full_coarea_ae_comp hd0 hdU 0 he,full_coarea_ae_comp hd0 hdU 1 he,
    full_coarea_ae_comp hd0 hdU 2 he,full_coarea_ae_comp hd0 hdU 3 he] with k h0 h1 h2 h3
  simp only [difference,h0,h1,h2,h3]

theorem source_near_kernel_L2_subsequence {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (u:ℕ→Source) {R:ℝ≥0∞} (hR:R≠⊤) (hbound:∀n,eLpNorm (u n) 2 circleHaar≤R)
    (henergy:Tendsto (fun n=>∫⁻k,‖difference (u n) k‖ₑ^2 ∂circleRegularCoarea d)
      atTop (𝓝 0)) :
    ∃f:Source,∃s:ℕ→ℕ,StrictMono s ∧ Tendsto (u∘s) atTop (𝓝 f) := by
  let φ : ℕ→PinnedPeriodicity.Circle→ℂ := fun n=>(Lp.aestronglyMeasurable (u n)).aemeasurable.mk (u n)
  have hm (n:ℕ) : Measurable (φ n) := (Lp.aestronglyMeasurable (u n)).aemeasurable.measurable_mk
  have he (n:ℕ) : (u n:PinnedPeriodicity.Circle→ℂ)=ᵐ[circleHaar]φ n :=
    (Lp.aestronglyMeasurable (u n)).aemeasurable.ae_eq_mk
  have hφ (n:ℕ) : MemLp (φ n) 2 circleHaar := (memLp_congr_ae (he n)).mp (Lp.memLp (u n))
  have hboundφ (n:ℕ) : eLpNorm (φ n) 2 circleHaar≤R := by
    rw [←eLpNorm_congr_ae (he n)]
    exact hbound n
  have henergyφ : Tendsto (fun n=>∫⁻k,‖difference (φ n) k‖ₑ^2 ∂circleRegularCoarea d)
      atTop (𝓝 0) := by
    convert henergy using 1
    funext n
    exact (unweighted_difference_energy_ae_eq hd0 hdU (he n)).symm
  obtain ⟨f,s,hs,hconv⟩ := PinnedLpCompactness.actual_near_kernel_L2_subsequence
    hd0 hdU hm hφ hR hboundφ henergyφ
  have ht (n:ℕ) : (hφ n).toLp (φ n)=u n :=
    Lp.ext ((hφ n).coeFn_toLp.trans (he n).symm)
  refine ⟨f,s,hs,?_⟩
  simpa only [ht,Function.comp_def] using hconv

theorem unweighted_energy_le_weighted (d:ℝ) (a:FourCircle→ℝ)
    {b:ℝ} (hb:0<b) (hlower:∀k,b≤a k) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀φ:PinnedPeriodicity.Circle→ℂ,
      (∫⁻k,‖difference φ k‖ₑ^2 ∂circleRegularCoarea d) ≤
        C*(∫⁻k,‖difference φ k‖ₑ^2 ∂weightedCoarea d a) := by
  have hb0 : ENNReal.ofReal b≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr hb)
  have hm := PinnedCompactGraph.restricted_measure_le_inverse_weight
    (euclideanCircleRegularCoarea d) MeasurableSet.univ hb0 ENNReal.ofReal_ne_top
    (w:=weight a) (fun k _=>ENNReal.ofReal_le_ofReal (hlower (fullLegs k)))
  simp only [Measure.restrict_univ] at hm
  have hμ : circleRegularCoarea d =
      (areaFactor:ℝ≥0∞)⁻¹ • euclideanCircleRegularCoarea d := by
    rw [euclideanCircleRegularCoarea_eq_smul,smul_smul,
      ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr areaFactor_ne_zero) ENNReal.coe_ne_top,one_smul]
  let C := (areaFactor:ℝ≥0∞)⁻¹*(ENNReal.ofReal b)⁻¹
  refine ⟨C,ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr areaFactor_ne_zero))
    (ENNReal.inv_ne_top.mpr hb0),?_⟩
  intro φ
  rw [hμ,lintegral_smul_measure]
  have hh : (∫⁻k,‖difference φ k‖ₑ^2 ∂euclideanCircleRegularCoarea d) ≤
      (ENNReal.ofReal b)⁻¹*(∫⁻k,‖difference φ k‖ₑ^2 ∂weightedCoarea d a) := by
    exact (lintegral_mono' hm le_rfl).trans_eq (lintegral_smul_measure _ _)
  simpa only [C,mul_assoc] using mul_le_mul_right hh ((areaFactor:ℝ≥0∞)⁻¹)

theorem positive_weight_lower_bound {a:FourCircle→ℝ} (ha:Continuous a)
    (hpos:∀k,0<a k) : ∃b:ℝ,0<b ∧ ∀k,b≤a k := by
  obtain ⟨k,_hk,hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty ha.continuousOn
  exact ⟨a k,hpos k,fun j=>hmin (Set.mem_univ j)⟩

/-- Actual compactness of every bounded original L² near-kernel sequence,
for the entire regular coarea and an arbitrary continuous positive quartet
weight.  No spectral gap or compact operator is supplied as a hypothesis. -/
theorem weighted_near_kernel_L2_subsequence {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (ha:Continuous a) (hpos:∀k,0<a k)
    (u:ℕ→Source) {R:ℝ≥0∞} (hR:R≠⊤) (hbound:∀n,eLpNorm (u n) 2 circleHaar≤R)
    (henergy:Tendsto (fun n=>∫⁻k,‖difference (u n) k‖ₑ^2 ∂weightedCoarea d a)
      atTop (𝓝 0)) :
    ∃f:Source,∃s:ℕ→ℕ,StrictMono s ∧ Tendsto (u∘s) atTop (𝓝 f) := by
  obtain ⟨b,hb,hlower⟩ := positive_weight_lower_bound ha hpos
  obtain ⟨C,hC,hdom⟩ := unweighted_energy_le_weighted d a hb hlower
  apply source_near_kernel_L2_subsequence hd0 hdU u hR hbound
  have ht := ENNReal.Tendsto.const_mul henergy (a:=C) (Or.inr hC)
  simp only [mul_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _=>zero_le _) (fun n=>hdom (u n))

end
end Resonance.PinnedWeightedCompactness
