import Resonance.PinnedFullAverageEnergy

/-! Finite actual-chart coverage and one common subsequence of the complete
three-source averages.  The chart family is obtained from the original
dispersion at every target; no compactness assertion is stored in a chart. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
namespace Resonance.PinnedFiniteAverages
noncomputable section
open Resonance.PinnedSmoothing Resonance.PinnedLocalSmooth
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedMeasure Resonance.PinnedFullAverage

structure AverageChart (d : ℝ) where
  center : ℝ
  source : ℝ
  radius : ℝ
  jacobian : ℝ
  H : ℝ×ℝ→ℝ
  ρ : ℝ→ℝ
  radius_pos : 0<radius
  jacobian_pos : 0<jacobian
  smooth : ContDiffOn ℝ ∞ H (Metric.ball center radius ×ˢ Metric.ball source radius)
  source_lower : ∀p∈Metric.ball center radius ×ˢ Metric.ball source radius,
    jacobian≤|partialZ H p| ∧ jacobian≤|partialZ H p-1|
  regular : ∀p∈Metric.ball center radius ×ˢ Metric.ball source radius,
    graph H p∈regularSurface d
  bump_smooth : ContDiff ℝ ∞ ρ
  bump_support : tsupport ρ ⊆ Metric.ball source (radius/8)
  bump_integral : (∫t in Icc (source-radius/4) (source+radius/4),ρ t)=1

namespace AverageChart
def target {d:ℝ} (C:AverageChart d) : Set ℝ :=
  Icc (C.center-C.radius/8) (C.center+C.radius/8)
def value {d:ℝ} (C:AverageChart d) (φ:PinnedPeriodicity.Circle→ℂ) : ℝ→ℂ :=
  fullAverage C.H C.ρ C.source C.radius φ

theorem target_compact {d:ℝ} (C:AverageChart d) : IsCompact C.target := isCompact_Icc
instance target_compactSpace {d:ℝ} (C:AverageChart d) : CompactSpace C.target :=
  isCompact_iff_compactSpace.mp C.target_compact
theorem target_subset {d:ℝ} (C:AverageChart d) :
    C.target ⊆ Metric.ball C.center (C.radius/4) := by
  rw [target,←Real.closedBall_eq_Icc]
  exact Metric.closedBall_subset_ball (by linarith [C.radius_pos])

theorem uniform_C1 {d:ℝ} (C:AverageChart d) :
    ∃C₀ C₁:ℝ≥0∞,C₀≠⊤ ∧ C₁≠⊤ ∧
      ∀φ:PinnedPeriodicity.Circle→ℂ,MemLp φ 2 circleHaar→∀x∈C.target,
        DifferentiableAt ℝ (C.value φ) x ∧
        ‖C.value φ x‖ₑ≤C₀*eLpNorm φ 2 circleHaar ∧
        ‖deriv (C.value φ) x‖ₑ≤C₁*eLpNorm φ 2 circleHaar := by
  obtain ⟨C₀,C₁,hC₀,hC₁,hall⟩ := full_average_L2_uniform_C1 C.radius_pos C.jacobian_pos
    C.smooth C.source_lower C.bump_smooth C.bump_support
  exact ⟨C₀,C₁,hC₀,hC₁,fun φ hφ x hx=>hall φ hφ x (C.target_subset hx)⟩

def asBounded {d:ℝ} (C:AverageChart d) (φ:PinnedPeriodicity.Circle→ℂ)
    (hφ:MemLp φ 2 circleHaar) : C.target→ᵇℂ := by
  refine BoundedContinuousFunction.mkOfCompact ⟨fun x=>C.value φ x,?_⟩
  obtain ⟨_C₀,_C₁,_hC₀,_hC₁,hall⟩ := C.uniform_C1
  exact continuousOn_iff_continuous_restrict.mp
    (fun x hx=>(hall φ hφ x hx).1.continuousAt.continuousWithinAt)

theorem asBounded_apply {d:ℝ} (C:AverageChart d) (φ:PinnedPeriodicity.Circle→ℂ)
    (hφ:MemLp φ 2 circleHaar) (x:C.target) : C.asBounded φ hφ x=C.value φ x := rfl

theorem energy_le {d:ℝ} (hd0:0<d) (hdU:d<1/2) (C:AverageChart d) :
    ∃B:ℝ≥0∞,B≠⊤ ∧ ∀φ:PinnedPeriodicity.Circle→ℂ,Measurable φ→MemLp φ 2 circleHaar→
      (∫⁻x in C.target,‖periodicLift φ x-C.value φ x‖ₑ^2) ≤
        B*(∫⁻k,‖PinnedMaximalDifference.difference φ k‖ₑ^2 ∂circleRegularCoarea d) :=
  PinnedFullAverageEnergy.full_average_local_energy_le hd0 hdU C.radius_pos C.jacobian_pos
    C.smooth C.source_lower C.regular C.bump_smooth.continuous C.bump_integral C.target_subset
end AverageChart

theorem actual_chart_at {d:ℝ} (hd0:0<d) (hdU:d<1/2) (x:ℝ) :
    ∃C:AverageChart d,C.center=x := by
  obtain ⟨y,z,H,r,κ,hr,hκ,_hbase,hs,hall⟩ := PinnedCharts.every_target_uniform_chart hd0 hdU x
  obtain ⟨ρ,hρ,_hc,hρsupp,hρone⟩ := exists_normalized_source_bump (z:=z) hr
  refine ⟨⟨x,z,r,κ,H,ρ,hr,hκ,hs,?_,?_,hρ,hρsupp,hρone⟩,rfl⟩
  · intro p hp
    exact (hall p hp).2.2
  · intro p hp
    apply graph_regular (hall p hp).1
    exact sub_ne_zero.mp (abs_pos.mp (lt_of_lt_of_le hκ (hall p hp).2.1))

/-- Finitely many of the genuine target charts cover the entire original
fundamental circle interval.  Their closed targets remain strictly inside
the source-averaging neighborhoods. -/
theorem finite_actual_chart_cover {d:ℝ} (hd0:0<d) (hdU:d<1/2) :
    ∃J:Finset ℝ,∃C:ℝ→AverageChart d,
      ∀x∈Icc 0 period,∃j∈J,x∈(C j).target := by
  classical
  choose C hC using actual_chart_at hd0 hdU
  let U : ℝ→Set ℝ := fun x=>Metric.ball (C x).center ((C x).radius/8)
  have hcover : Icc 0 period ⊆ ⋃x,U x := by
    intro x _hx
    apply mem_iUnion.mpr
    refine ⟨x,?_⟩
    simp only [U,hC x,Metric.mem_ball,dist_self]
    exact div_pos (C x).radius_pos (by norm_num)
  obtain ⟨J,hJ⟩ := isCompact_Icc.elim_finite_subcover U (fun _=>Metric.isOpen_ball) hcover
  refine ⟨J,C,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hJ hx)
  obtain ⟨hjJ,hxj⟩ := mem_iUnion.mp hj
  refine ⟨j,hjJ,?_⟩
  rw [AverageChart.target,←Real.closedBall_eq_Icc]
  exact Metric.ball_subset_closedBall hxj

/-- All members of a finite actual chart family converge along one common
subsequence.  This is finite-product compactness of the complete signed
averages, not independent subsequences subsequently identified. -/
theorem finite_average_common_subsequence {ι:Type*} [Fintype ι] {d:ℝ}
    (C:ι→AverageChart d) {φ:ℕ→PinnedPeriodicity.Circle→ℂ}
    (hφ:∀n,MemLp (φ n) 2 circleHaar)
    {R:ℝ≥0∞} (hR:R≠⊤) (hbound:∀n,eLpNorm (φ n) 2 circleHaar≤R) :
    ∃g:(i:ι)→(C i).target→ᵇℂ,∃s:ℕ→ℕ,StrictMono s ∧
      ∀i,TendstoUniformly (fun n (x:(C i).target)=>(C i).value (φ (s n)) x) (g i) atTop := by
  choose B₀ B₁ hB₀ hB₁ hall using fun i=>(C i).uniform_C1
  let A : ℕ→(i:ι)→(C i).target→ᵇℂ := fun n i=>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x=>(C i).value (φ n) x,
        continuousOn_iff_continuous_restrict.mp
          (fun x hx=>(hall i (φ n) (hφ n) x hx).1.continuousAt.continuousWithinAt)⟩
  have hb₀ (i:ι) (n:ℕ) (x:(C i).target) :
      ‖A n i x‖₊≤(B₀ i*R).toNNReal := by
    apply ENNReal.le_toNNReal_of_coe_le _ (ENNReal.mul_ne_top (hB₀ i) hR)
    exact (hall i (φ n) (hφ n) x x.2).2.1.trans (mul_le_mul_right (hbound n) (B₀ i))
  have hLip (i:ι) (n:ℕ) : LipschitzWith (B₁ i*R).toNNReal (A n i) := by
    have hh := (convex_Icc ((C i).center-(C i).radius/8)
      ((C i).center+(C i).radius/8)).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx=>(hall i (φ n) (hφ n) x hx).1)
      (fun x hx=>ENNReal.le_toNNReal_of_coe_le
        ((hall i (φ n) (hφ n) x hx).2.2.trans (mul_le_mul_right (hbound n) (B₁ i)))
        (ENNReal.mul_ne_top (hB₁ i) hR))
    intro x y
    exact hh x.2 y.2
  have hc (i:ι) : IsCompact (closure (range (fun n=>A n i))) := by
    have hequi : Equicontinuous ((↑) : range (fun n=>A n i)→(C i).target→ℂ) := by
      apply Metric.equicontinuous_of_continuity_modulus
        (fun r=>((B₁ i*R).toNNReal:ℝ)*r)
        (by simpa using (continuous_const.mul continuous_id :
          Continuous (fun r:ℝ=>((B₁ i*R).toNNReal:ℝ)*r)).tendsto 0)
      intro x y f
      obtain ⟨n,hn⟩ := f.2
      simpa [←hn] using (hLip i n).dist_le_mul x y
    exact BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0:ℂ) (B₀ i*R).toNNReal)
      (isCompact_closedBall (0:ℂ) (B₀ i*R).toNNReal)
      (range (fun n=>A n i))
      (by
        intro f x hf
        obtain ⟨n,rfl⟩ := hf
        simpa only [Metric.mem_closedBall,dist_zero_right] using hb₀ i n x)
      hequi
  have hcompact := isCompact_pi_infinite hc
  obtain ⟨g,_hg,s,hs,hconv⟩ := hcompact.tendsto_subseq
    (x:=A) (fun n i=>subset_closure (mem_range_self n))
  refine ⟨g,s,hs,?_⟩
  intro i
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((tendsto_pi_nhds.mp hconv) i)

end
end Resonance.PinnedFiniteAverages
