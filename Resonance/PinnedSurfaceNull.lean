import Resonance.PinnedMeasure

/-! Null-set tools for the complete regular pinned resonance surface.
These lemmas use genuine Hausdorff measure, not a chart-defined replacement. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedSurfaceNull
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedCharts Resonance.PinnedMeasure

theorem real_hausdorff_two_zero (S : Set ℝ) : (μH[2] : Measure ℝ) S = 0 := by
  have hu : (μH[2] : Measure ℝ) univ = 0 := by
    apply measure_null_of_locally_null univ
    intro x _
    have hz : (μH[2] : Measure ℝ) (Ioo (x-1) (x+1)) = 0 := by
      rcases Measure.hausdorffMeasure_zero_or_top (by norm_num : (1:ℝ)<2)
        (Ioo (x-1) (x+1)) with h | h
      · exact h
      · rw [hausdorffMeasure_real,Real.volume_Ioo] at h
        exact (ENNReal.ofReal_ne_top h).elim
    exact ⟨Ioo (x-1) (x+1),mem_nhdsWithin_of_mem_nhds
      (Ioo_mem_nhds (by linarith) (by linarith)),hz⟩
  exact measure_mono_null (subset_univ S) hu

theorem smooth_curve_local_null {γ : ℝ → Ambient} {t : ℝ}
    (hγ : ContDiffAt ℝ 1 γ t) :
    ∃ I ∈ 𝓝 t, (μH[2] : Measure Ambient) (γ '' I) = 0 := by
  obtain ⟨K,I,hI,hLip⟩ := hγ.exists_lipschitzOnWith
  refine ⟨I,hI,le_antisymm ?_ (zero_le _)⟩
  have hb := hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2)
  rw [real_hausdorff_two_zero,mul_zero] at hb
  exact hb

theorem graph_null_over_first {H : ℝ×ℝ → ℝ} {U : Set (ℝ×ℝ)} {K : ℝ≥0}
    (hLip : LipschitzOnWith K (graph H) U)
    {E : Set ℝ} (_hE : MeasurableSet E) (hnull : volume E=0) :
    (μH[2] : Measure Ambient) (graph H '' (U ∩ (E ×ˢ univ))) = 0 := by
  have hprod : (volume : Measure (ℝ×ℝ)) (E ×ˢ univ) = 0 := by
    change (volume.prod volume) (E ×ˢ univ) = 0
    rw [Measure.prod_prod E univ,hnull,zero_mul]
  have hsource : (μH[2] : Measure (ℝ×ℝ)) (U ∩ (E ×ˢ univ)) = 0 := by
    rw [hausdorffMeasure_prod_real]
    exact measure_mono_null inter_subset_right hprod
  have hb := (hLip.mono (show U ∩ (E ×ˢ univ) ⊆ U from inter_subset_left)).hausdorffMeasure_image_le
    (by norm_num : (0:ℝ)≤2)
  rw [hsource,mul_zero] at hb
  exact le_antisymm hb (zero_le _)

/-- The actual implicit graph contains every nearby zero of the original energy.
This is stronger than merely constructing one branch through the point. -/
theorem exact_resonance_graph {d x y z : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (he : energyDefect d x y z=0)
    (hy : velocity d y ≠ velocity d (x+y-z)) :
    ∃ H : ℝ×ℝ→ℝ,
      H (x,z)=y ∧ ContDiffAt ℝ ω H (x,z) ∧
      (∀ᶠ q : ChartInput in 𝓝 ((x,z),y),
        energyDefect d q.1.1 q.2 q.1.2=0 ↔ H q.1=q.2) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  let p : ChartInput := ((x,z),y)
  have hc : ContDiffAt ℝ ω (chartFunction d) p :=
    (chartFunction_contDiff hdL hdU ω).contDiffAt
  have hi := partial_y_invertible hdL hdU p hy
  let H := hc.implicitFunction (by simp) hi
  refine ⟨H,hc.implicitFunction_apply_self (by simp) hi,
    hc.contDiffAt_implicitFunction (by simp) hi,?_⟩
  simpa only [chartFunction,p,he] using
    hc.eventually_apply_eq_iff_implicitFunction (by simp) hi

/-- Where the y-partial is nonzero, the entire original energy surface has
an absolutely continuous x-projection. -/
theorem good_first_projection_null {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {E : Set ℝ} (hE : MeasurableSet E) (hnull : volume E=0) :
    (μH[2] : Measure Ambient)
      {k | liftedEnergy d k=0 ∧ k 0∈E ∧
        velocity d (k 1)≠velocity d (k 0+k 1-k 2)}=0 := by
  let S : Set Ambient := {k | liftedEnergy d k=0 ∧ k 0∈E ∧
    velocity d (k 1)≠velocity d (k 0+k 1-k 2)}
  change (μH[2] : Measure Ambient) S=0
  apply measure_null_of_locally_null S
  intro k hk
  obtain ⟨H,_hbase,hH,hiff⟩ := exact_resonance_graph hd0 hdU hk.1 hk.2.2
  have hg : ContDiffAt ℝ 1 (graph H) (k 0,k 2) := by
    rw [contDiffAt_piLp]
    intro i
    fin_cases i
    · exact contDiffAt_fst
    · exact hH.of_le (by norm_num)
    · exact contDiffAt_snd
  obtain ⟨K,U,hU,hLip⟩ := hg.exists_lipschitzOnWith
  have hz := graph_null_over_first hLip hE hnull
  have hp : Continuous (fun q : Ambient => ((q 0,q 2),q 1)) :=
    ((coordinateProjection 0).continuous.prodMk (coordinateProjection 2).continuous
      ).prodMk (coordinateProjection 1).continuous
  have hnear : ∀ᶠ q : Ambient in 𝓝 k,
      (q 0,q 2)∈U ∧ (liftedEnergy d q=0 ↔ H (q 0,q 2)=q 1) :=
    ((targetProjection.continuous.continuousAt.tendsto.eventually hU).and
      (hp.continuousAt.tendsto.eventually hiff))
  let V := S ∩ {q : Ambient | (q 0,q 2)∈U ∧
    (liftedEnergy d q=0 ↔ H (q 0,q 2)=q 1)}
  refine ⟨V,inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hnear),?_⟩
  apply measure_mono_null _ hz
  rintro q ⟨hq,hqU,hqi⟩
  refine ⟨(q 0,q 2),⟨hqU,hq.2.1,mem_univ _⟩,?_⟩
  have heq := hqi.mp hq.1
  ext i
  fin_cases i <;> simp [graph,heq]

end
end Resonance.PinnedSurfaceNull
