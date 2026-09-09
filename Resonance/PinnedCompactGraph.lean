import Resonance.PinnedMeasureNormalization
import Resonance.PinnedLocalSmooth

/-! Quantitative control of compact pieces of the actual pinned resonance
graphs by the complete regular coarea.  Unlike a mere null-set transfer,
the estimate retains the compact graph-image restriction; integration of
periodic data over the whole real lift is not used as a finite circle bound. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal MeasureTheory Topology
namespace Resonance.PinnedCompactGraph
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure

theorem restricted_measure_le_inverse_weight
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {K : Set X}
    (hK : MeasurableSet K) {w : X → ℝ≥0∞} {b : ℝ≥0∞}
    (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) (hb : ∀ x∈K, b ≤ w x) :
    μ.restrict K ≤ b⁻¹ • (μ.withDensity w).restrict K := by
  have hh : b • μ.restrict K ≤ (μ.restrict K).withDensity w := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK] with x hx
    exact hb x hx
  rw [← restrict_withDensity hK] at hh
  apply Measure.le_iff.mpr
  intro E _hE
  calc
    μ.restrict K E = b⁻¹ * (b * μ.restrict K E) :=
      (ENNReal.inv_mul_cancel_left hb0 hbtop).symm
    _ ≤ b⁻¹ * ((μ.withDensity w).restrict K E) := by
      gcongr
      exact hh E
    _ = (b⁻¹ • (μ.withDensity w).restrict K) E := rfl

/-- A compact regular piece has a genuine positive lower bound for the
original coarea weight; only the actual continuous gradient is bounded. -/
theorem compact_coarea_weight_lower {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {K : Set Ambient} (hK : IsCompact K) (hreg : K ⊆ regularSurface d) :
    ∃ b : ℝ≥0∞, b ≠ 0 ∧ b ≠ ⊤ ∧ ∀ k∈K, b ≤ coareaWeight d k := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (energyGradient_continuous hd0 hdU).continuousOn
  let M := max B 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let b : ℝ≥0∞ := ENNReal.ofReal (((2*Real.pi)^3*M)⁻¹)
  have hb : 0 < ((2*Real.pi)^3*M)⁻¹ := by positivity
  refine ⟨b,ne_of_gt (ENNReal.ofReal_pos.mpr hb),ENNReal.ofReal_ne_top,?_⟩
  intro k hk
  apply ENNReal.ofReal_le_ofReal
  simp only [← one_div]
  apply one_div_le_one_div_of_le
  · exact mul_pos (by positivity) (norm_pos_iff.mpr (hreg hk).2)
  · exact mul_le_mul_of_nonneg_left ((hB k hk).trans (le_max_left _ _)) (by positivity)

theorem compact_regular_hausdorff_le_coarea {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2)
    {K : Set Ambient} (hK : IsCompact K) (hreg : K ⊆ regularSurface d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (μH[2] : Measure Ambient).restrict K ≤ C • (liftedRegularCoarea d).restrict K := by
  obtain ⟨b,hb0,hbtop,hb⟩ := compact_coarea_weight_lower hd0 hdU hK hreg
  refine ⟨b⁻¹,ENNReal.inv_ne_top.mpr hb0,?_⟩
  have hh := restricted_measure_le_inverse_weight
    ((μH[2] : Measure Ambient).restrict (regularSurface d)) hK.measurableSet hb0 hbtop hb
  rw [Measure.restrict_restrict_of_subset hreg] at hh
  exact hh

/-- The quantitative counterpart of `graph_preimage_null`, with a compact
source rectangle or any compact source subset.  The full coarea and the
same graph image are retained, including possible overlap with other charts. -/
theorem compact_graph_map_le_coarea {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) (H : ℝ×ℝ → ℝ)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (hH : ContinuousOn H S)
    (hreg : ∀ p∈S, graph H p ∈ regularSurface d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (volume.restrict S).map (graph H) ≤
        C • (liftedRegularCoarea d).restrict (graph H '' S) := by
  have hg : ContinuousOn (graph H) S := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact continuous_fst.continuousOn
    · exact hH
    · exact continuous_snd.continuousOn
  let K := graph H '' S
  have hK : IsCompact K := hS.image_of_continuousOn hg
  have hKr : K ⊆ regularSurface d := by
    rintro _ ⟨p,hp,rfl⟩
    exact hreg p hp
  obtain ⟨B,hB,hbound⟩ := compact_regular_hausdorff_le_coarea hd0 hdU hK hKr
  let L : ℝ≥0∞ := (‖targetProjection‖₊ : ℝ≥0∞) ^ (2:ℝ)
  have hL : L ≠ ⊤ := by
    exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
  refine ⟨L*B,ENNReal.mul_ne_top hL hB,?_⟩
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply_of_aemeasurable (hg.aemeasurable hS.measurableSet) hE,
    Measure.restrict_apply' hS.measurableSet]
  have hproj := targetProjection.lipschitz.hausdorffMeasure_image_le
    (by norm_num : (0:ℝ)≤2) (E∩K)
  rw [hausdorffMeasure_prod_real] at hproj
  have hsub : (graph H ⁻¹' E)∩S ⊆ targetProjection '' (E∩K) := by
    rintro p ⟨hpE,hpS⟩
    exact ⟨graph H p,⟨hpE,⟨p,hpS,rfl⟩⟩,targetProjection_graph H p⟩
  calc
    volume ((graph H ⁻¹' E)∩S) ≤ volume (targetProjection '' (E∩K)) := measure_mono hsub
    _ ≤ L*(μH[2] : Measure Ambient) (E∩K) := hproj
    _ = L*((μH[2] : Measure Ambient).restrict K E) := by
      rw [Measure.restrict_apply' hK.measurableSet]
    _ ≤ L*((B • (liftedRegularCoarea d).restrict K) E) := by
      gcongr
    _ = ((L*B) • (liftedRegularCoarea d).restrict K) E := by
      simp only [Measure.smul_apply, smul_eq_mul, mul_assoc]

/-- The complete four-leg difference, before any square or averaging. -/
def completeDifference (f : ℝ→ℂ) (k : Ambient) : ℂ :=
  f (k 0)+f (k 1)-f (k 2)-f (k 0+k 1-k 2)

theorem completeDifference_measurable {f : ℝ→ℂ} (hf : Measurable f) :
    Measurable (completeDifference f) := by
  unfold completeDifference
  exact ((hf.comp (coordinateProjection 0).continuous.measurable).add
    (hf.comp (coordinateProjection 1).continuous.measurable)).sub
      (hf.comp (coordinateProjection 2).continuous.measurable) |>.sub
        (hf.comp (((coordinateProjection 0).continuous.add
          (coordinateProjection 1).continuous).sub (coordinateProjection 2).continuous).measurable)

/-- Quantitative graph control is applied once to the square of the full
signed difference.  Individual legs are not estimated independently here. -/
theorem compact_graph_complete_energy_le {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) (H : ℝ×ℝ → ℝ)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (hH : ContinuousOn H S)
    (hreg : ∀ p∈S, graph H p ∈ regularSurface d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℝ→ℂ, Measurable f →
      (∫⁻ p in S, ‖f p.1+f (H p)-f p.2-f (p.1+H p-p.2)‖ₑ^2) ≤
        C*(∫⁻ k in graph H '' S, ‖completeDifference f k‖ₑ^2 ∂liftedRegularCoarea d) := by
  obtain ⟨C,hC,hbound⟩ := compact_graph_map_le_coarea hd0 hdU H hS hH hreg
  refine ⟨C,hC,?_⟩
  intro f hf
  have hg : ContinuousOn (graph H) S := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact continuous_fst.continuousOn
    · exact hH
    · exact continuous_snd.continuousOn
  have hF : Measurable (fun k => ‖completeDifference f k‖ₑ^2) :=
    (completeDifference_measurable hf).enorm.pow_const 2
  change (∫⁻ p in S, ‖completeDifference f (graph H p)‖ₑ^2) ≤ _
  rw [← lintegral_map' hF.aemeasurable (hg.aemeasurable hS.measurableSet)]
  calc
    _ ≤ ∫⁻ k, ‖completeDifference f k‖ₑ^2 ∂C •
        (liftedRegularCoarea d).restrict (graph H '' S) := lintegral_mono' hbound le_rfl
    _ = _ := lintegral_smul_measure C _

end
end Resonance.PinnedCompactGraph
