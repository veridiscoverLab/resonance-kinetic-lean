import Resonance.PinnedCriticalFactor
import Resonance.PinnedSurfaceNull

/-! Actual local Hausdorff-area bounds for implicit graphs used in the pinned
critical cancellation. All graphs below come from the inverse function theorem. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedLocalArea
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedCharts Resonance.PinnedMeasure
open Resonance.PinnedCriticalFactor

theorem c1_surface_local_finite_area {γ : ℝ×ℝ→Ambient} {p : ℝ×ℝ}
    (hγ : ContDiffAt ℝ 1 γ p) :
    ∃ U ∈ 𝓝 p, (μH[2] : Measure Ambient) (γ '' U)<(∞:ℝ≥0∞) := by
  obtain ⟨K,U,hU,hLip⟩ := hγ.exists_lipschitzOnWith
  let V := U ∩ Metric.closedBall p 1
  have hV : V ∈ 𝓝 p := inter_mem hU (Metric.closedBall_mem_nhds p (by norm_num))
  have hm : (μH[2] : Measure (ℝ×ℝ)) V<(∞:ℝ≥0∞) := by
    rw [hausdorffMeasure_prod_real]
    exact lt_of_le_of_lt (measure_mono inter_subset_right)
      (isCompact_closedBall p 1).measure_lt_top
  have hb := (hLip.mono (show V ⊆ U from inter_subset_left)).hausdorffMeasure_image_le
    (by norm_num : (0:ℝ)≤2)
  refine ⟨V,hV,lt_of_le_of_lt hb ?_⟩
  apply ENNReal.mul_lt_top _ hm
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simp)

theorem scalar_partial_invertible {F : ChartInput→ℝ} {p : ChartInput}
    (hF : DifferentiableAt ℝ F p)
    (hn : deriv (fun t : ℝ => F (p.1,t)) p.2≠0) :
    ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ (ℝ×ℝ) ℝ)).IsInvertible := by
  let L := (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ (ℝ×ℝ) ℝ)
  have hs := hF.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hL : L 1≠0 := by
    change (fderiv ℝ F p) (0,1)≠0
    change HasDerivAt (fun t : ℝ => F (p.1,t)) ((fderiv ℝ F p) (0,1)) p.2 at hs
    rw [←hs.deriv]
    exact hn
  have hi : Function.Injective L := by
    intro a b he
    have hLa : L a=a*L 1 := by
      calc L a=L (a • (1:ℝ)) := by simp
           _=a • L 1 := L.map_smul a 1
           _=a*L 1 := rfl
    have hLb : L b=b*L 1 := by
      calc L b=L (b • (1:ℝ)) := by simp
           _=b • L 1 := L.map_smul b 1
           _=b*L 1 := rfl
    rw [hLa,hLb] at he
    exact mul_right_cancel₀ hL he
  let e : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofBijective L.toLinearMap
      ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  exact ⟨e,rfl⟩

theorem exact_c1_graph {F : ChartInput→ℝ} {p : ChartInput}
    (hF : ContDiffAt ℝ 1 F p)
    (hn : deriv (fun t : ℝ => F (p.1,t)) p.2≠0) :
    ∃ H : ℝ×ℝ→ℝ, H p.1=p.2 ∧ ContDiffAt ℝ 1 H p.1 ∧
      (∀ᶠ q in 𝓝 p, F q=F p ↔ H q.1=q.2) := by
  have hi := scalar_partial_invertible (hF.differentiableAt (by norm_num)) hn
  let H := hF.implicitFunction (by norm_num) hi
  exact ⟨H,hF.implicitFunction_apply_self (by norm_num) hi,
    hF.contDiffAt_implicitFunction (by norm_num) hi,
    hF.eventually_apply_eq_iff_implicitFunction (by norm_num) hi⟩

def firstAssemble : ChartInput→L[ℝ] Ambient :=
  ({ toFun := fun q => WithLp.toLp 2 ![q.2,q.1.1,q.1.2]
     map_add' := by intros; ext i; fin_cases i <;> rfl
     map_smul' := by intros; ext i; fin_cases i <;> rfl } : ChartInput→ₗ[ℝ] Ambient).toContinuousLinearMap

def firstSplit : Ambient→L[ℝ] ChartInput :=
  ({ toFun := fun p => ((p 1,p 2),p 0)
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Ambient→ₗ[ℝ] ChartInput).toContinuousLinearMap

def firstGraph (H : ℝ×ℝ→ℝ) (p : ℝ×ℝ) : Ambient :=
  WithLp.toLp 2 ![H p,p.1,p.2]

theorem firstGraph_contDiffAt {H : ℝ×ℝ→ℝ} {p : ℝ×ℝ}
    (hH : ContDiffAt ℝ 1 H p) : ContDiffAt ℝ 1 (firstGraph H) p := by
  rw [contDiffAt_piLp]
  intro i
  fin_cases i
  · exact hH
  · exact contDiffAt_fst
  · exact contDiffAt_snd

/-- A nonzero first partial gives locally finite area of the entire zero set,
not just the branch chosen by the implicit-function constructor. -/
theorem first_partial_zero_set_finite_area {F : Ambient→ℝ} {p : Ambient}
    (hF : ContDiffAt ℝ 1 F p) (hzero : F p=0)
    (hn : deriv (fun t : ℝ => F (WithLp.toLp 2 ![t,p 1,p 2])) (p 0)≠0) :
    ∃ U ∈ 𝓝 p, (μH[2] : Measure Ambient) (U ∩ {k | F k=0})<(∞:ℝ≥0∞) := by
  have hId : ∀q : Ambient, firstAssemble (firstSplit q)=q := by
    intro q; ext i; fin_cases i <;> rfl
  have hF' : ContDiffAt ℝ 1 F (firstAssemble (firstSplit p)) := by
    rw [hId]; exact hF
  have hFc : ContDiffAt ℝ 1 (fun q => F (firstAssemble q)) (firstSplit p) :=
    hF'.comp _ firstAssemble.contDiff.contDiffAt
  obtain ⟨H,hH0,hH,hiff⟩ := exact_c1_graph hFc hn
  obtain ⟨V,hV,harea⟩ := c1_surface_local_finite_area (firstGraph_contDiffAt hH)
  have hnear : ∀ᶠ q : Ambient in 𝓝 p,
      (q 1,q 2)∈V ∧ (F q=0 ↔ H (q 1,q 2)=q 0) := by
    have hproj : Continuous (fun q : Ambient => (q 1,q 2)) :=
      (coordinateProjection 1).continuous.prodMk (coordinateProjection 2).continuous
    have ha := firstSplit.continuous.continuousAt.tendsto.eventually hiff
    simp only [hId,hzero] at ha
    exact (hproj.continuousAt.tendsto.eventually hV).and ha
  let U := {q : Ambient | (q 1,q 2)∈V ∧ (F q=0 ↔ H (q 1,q 2)=q 0)}
  refine ⟨U,hnear,lt_of_le_of_lt (measure_mono ?_) harea⟩
  rintro q ⟨⟨hqV,hqi⟩,hq0⟩
  refine ⟨(q 1,q 2),hqV,?_⟩
  have he := hqi.mp hq0
  ext i
  fin_cases i <;> simp [firstGraph,he]

theorem graph_condition_locally_finite_area {P : Ambient→ℝ×ℝ} {γ : ℝ×ℝ→Ambient}
    (hP : Continuous P) {p : Ambient} (hγ : ContDiffAt ℝ 1 γ (P p)) :
    ∃ U ∈ 𝓝 p, (μH[2] : Measure Ambient) (U ∩ {q | γ (P q)=q})<(∞:ℝ≥0∞) := by
  obtain ⟨V,hV,harea⟩ := c1_surface_local_finite_area hγ
  refine ⟨P ⁻¹' V,hP.continuousAt.tendsto.eventually hV,
    lt_of_le_of_lt (measure_mono ?_) harea⟩
  rintro q ⟨hqV,hq⟩
  exact ⟨P q,hqV,hq⟩

theorem coordinate_planes_locally_finite_area (p : Ambient) :
    ∃ U ∈ 𝓝 p, (μH[2] : Measure Ambient)
      (U ∩ {q | q 1=0 ∨ q 2=0})<(∞:ℝ≥0∞) := by
  let P1 : Ambient→ℝ×ℝ := fun q => (q 0,q 2)
  let P2 : Ambient→ℝ×ℝ := fun q => (q 0,q 1)
  let γ1 : ℝ×ℝ→Ambient := fun q => WithLp.toLp 2 ![q.1,0,q.2]
  let γ2 : ℝ×ℝ→Ambient := fun q => WithLp.toLp 2 ![q.1,q.2,0]
  have hP1 : Continuous P1 :=
    (coordinateProjection 0).continuous.prodMk (coordinateProjection 2).continuous
  have hP2 : Continuous P2 :=
    (coordinateProjection 0).continuous.prodMk (coordinateProjection 1).continuous
  have hγ1 : ContDiffAt ℝ 1 γ1 (P1 p) := by
    rw [contDiffAt_piLp]; intro i; fin_cases i <;> dsimp [γ1] <;> fun_prop
  have hγ2 : ContDiffAt ℝ 1 γ2 (P2 p) := by
    rw [contDiffAt_piLp]; intro i; fin_cases i <;> dsimp [γ2] <;> fun_prop
  obtain ⟨U1,hU1,hA1⟩ := graph_condition_locally_finite_area hP1 hγ1
  obtain ⟨U2,hU2,hA2⟩ := graph_condition_locally_finite_area hP2 hγ2
  refine ⟨U1∩U2,inter_mem hU1 hU2,lt_of_le_of_lt (measure_mono ?_)
    (lt_of_le_of_lt (measure_union_le _ _) (ENNReal.add_lt_top.mpr ⟨hA1,hA2⟩))⟩
  rintro q ⟨⟨hq1,hq2⟩,hq|hq⟩
  · left; refine ⟨hq1,?_⟩; ext i; fin_cases i <;> simp [P1,γ1,hq]
  · right; refine ⟨hq2,?_⟩; ext i; fin_cases i <;> simp [P2,γ2,hq]

def rectangleEnergy (d : ℝ) (p : Ambient) : ℝ :=
  energyDefect d (p 0+p 1) (p 0+p 2) (p 0)

theorem rectangleEnergy_factor {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (p : Ambient) :
    rectangleEnergy d p= -p 1*p 2*sharedFactor d p := by
  have he : WithLp.toLp 2 ![p 0,p 1,p 2]=p := by ext i; fin_cases i <;> rfl
  simpa only [he] using pinned_energy_shared_factor hd0 hdU (p 0) (p 1) (p 2)

theorem rectangle_zero_set_decomposition {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (p : Ambient) :
    rectangleEnergy d p=0 ↔ p 1=0 ∨ p 2=0 ∨ sharedFactor d p=0 := by
  rw [rectangleEnergy_factor hd0 hdU]
  simp only [mul_eq_zero,neg_eq_zero]
  tauto

/-- Each of the two critical alternatives has finite local area for its entire
energy-zero set. Both trivial planes are retained in this area estimate. -/
theorem rectangle_zero_set_locally_finite_area {d : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (p : Ambient)
    (hgood : sharedFactor d p≠0 ∨
      deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,p 1,p 2])) (p 0)≠0) :
    ∃ U ∈ 𝓝 p, (μH[2] : Measure Ambient)
      (U ∩ {q | rectangleEnergy d q=0})<(∞:ℝ≥0∞) := by
  obtain ⟨V,hV,hA⟩ := coordinate_planes_locally_finite_area p
  by_cases hG : sharedFactor d p=0
  · have hD := hgood.resolve_left (not_not.mpr hG)
    obtain ⟨W,hW,hB⟩ := first_partial_zero_set_finite_area
      (sharedFactor_contDiff_one hd0 hdU).contDiffAt hG hD
    refine ⟨V∩W,inter_mem hV hW,lt_of_le_of_lt (measure_mono ?_)
      (lt_of_le_of_lt (measure_union_le _ _) (ENNReal.add_lt_top.mpr ⟨hA,hB⟩))⟩
    rintro q ⟨⟨hqV,hqW⟩,hq⟩
    rcases (rectangle_zero_set_decomposition hd0 hdU q).mp hq with h | h | h
    · exact Or.inl ⟨hqV,Or.inl h⟩
    · exact Or.inl ⟨hqV,Or.inr h⟩
    · exact Or.inr ⟨hqW,h⟩
  · have hnear : ∀ᶠ q in 𝓝 p, sharedFactor d q≠0 :=
      (sharedFactor_contDiff_one hd0 hdU).continuous.continuousAt.eventually_ne hG
    refine ⟨V∩{q | sharedFactor d q≠0},inter_mem hV hnear,
      lt_of_le_of_lt (measure_mono ?_) hA⟩
    rintro q ⟨⟨hqV,hqG⟩,hq⟩
    refine ⟨hqV,?_⟩
    rcases (rectangle_zero_set_decomposition hd0 hdU q).mp hq with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hqG h).elim

theorem local_area_transport {F G : Ambient→ℝ} {e g : Ambient→Ambient} {K : ℝ≥0}
    (hLip : LipschitzWith K e) (hg : Continuous g) (hInv : ∀q, e (g q)=q)
    (hFG : ∀q, G (g q)=F q) (p : Ambient)
    (hA : ∃ V ∈ 𝓝 (g p), (μH[2] : Measure Ambient)
      (V ∩ {q | G q=0})<(∞:ℝ≥0∞)) :
    ∃ U ∈ 𝓝 p, (μH[2] : Measure Ambient)
      (U ∩ {q | F q=0})<(∞:ℝ≥0∞) := by
  obtain ⟨V,hV,harea⟩ := hA
  have hb := hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2)
    (V ∩ {q | G q=0})
  have hfinite : (μH[2] : Measure Ambient) (e '' (V ∩ {q | G q=0}))<(∞:ℝ≥0∞) := by
    apply lt_of_le_of_lt hb
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simp)) harea
  refine ⟨g ⁻¹' V,hg.continuousAt.tendsto.eventually hV,
    lt_of_le_of_lt (measure_mono ?_) hfinite⟩
  rintro q ⟨hqV,hqF⟩
  exact ⟨g q,⟨hqV,by change G (g q)=0; rw [hFG]; exact hqF⟩,hInv q⟩

theorem regular_y_zero_set_finite_area {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {p : Ambient} (he : liftedEnergy d p=0)
    (hy : velocity d (p 1)≠velocity d (p 0+p 1-p 2)) :
    ∃ U ∈ 𝓝 p, (μH[2] : Measure Ambient)
      (U ∩ {q | liftedEnergy d q=0})<(∞:ℝ≥0∞) := by
  obtain ⟨H,_hbase,hH,hiff⟩ := PinnedSurfaceNull.exact_resonance_graph hd0 hdU he hy
  have hgraph : ContDiffAt ℝ 1 (graph H) (p 0,p 2) := by
    rw [contDiffAt_piLp]
    intro i
    fin_cases i
    · exact contDiffAt_fst
    · exact hH.of_le (by norm_num)
    · exact contDiffAt_snd
  obtain ⟨V,hV,harea⟩ := c1_surface_local_finite_area hgraph
  have hp : Continuous (fun q : Ambient => ((q 0,q 2),q 1)) :=
    ((coordinateProjection 0).continuous.prodMk (coordinateProjection 2).continuous
      ).prodMk (coordinateProjection 1).continuous
  have hnear : ∀ᶠ q : Ambient in 𝓝 p,
      (q 0,q 2)∈V ∧ (liftedEnergy d q=0 ↔ H (q 0,q 2)=q 1) :=
    ((targetProjection.continuous.continuousAt.tendsto.eventually hV).and
      (hp.continuousAt.tendsto.eventually hiff))
  let U := {q : Ambient | (q 0,q 2)∈V ∧ (liftedEnergy d q=0 ↔ H (q 0,q 2)=q 1)}
  refine ⟨U,hnear,lt_of_le_of_lt (measure_mono ?_) harea⟩
  rintro q ⟨⟨hqV,hqi⟩,hq0⟩
  refine ⟨(q 0,q 2),hqV,?_⟩
  have heq := hqi.mp hq0
  ext i
  fin_cases i <;> simp [graph,heq]

end
end Resonance.PinnedLocalArea
