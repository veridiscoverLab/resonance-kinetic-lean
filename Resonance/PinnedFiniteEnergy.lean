import Resonance.PinnedCriticalCancellation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Finite energy of actual periodic C² four-leg differences for the original
regular coarea. The proof uses cancellation before integration. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace Resonance.PinnedFiniteEnergy
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedSurfaceArea Resonance.PinnedCriticalCancellation

def zeroSurfaceMeasure (d : ℝ) : Measure Ambient :=
  (μH[2] : Measure Ambient).restrict {k | liftedEnergy d k=0}

theorem zeroSurface_locallyFinite {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    IsLocallyFiniteMeasure (zeroSurfaceMeasure d) := by
  have hZ : MeasurableSet {q : Ambient | liftedEnergy d q=0} :=
    (liftedEnergy_continuous hd0 hdU).measurable (measurableSet_singleton 0)
  constructor
  intro k
  obtain ⟨U,hU,hA⟩ := energy_zero_set_locally_finite_area hd0 hdU k
  exact ⟨U,hU,by simpa only [zeroSurfaceMeasure,Measure.restrict_apply' hZ] using hA⟩

theorem locallyIntegrable_of_local_bound {μ : Measure Ambient} [IsLocallyFiniteMeasure μ]
    {f : Ambient→ℝ} (hf : Measurable f)
    (hb : ∀p, ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 p, ‖f q‖≤C) :
    LocallyIntegrable f μ := by
  intro p
  obtain ⟨C,hC,hnear⟩ := hb p
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let V := Metric.closedBall p (r/2)
  have hV : V ∈ 𝓝 p := Metric.closedBall_mem_nhds p (half_pos hr)
  have hμV : μ V≠(∞:ℝ≥0∞) := (isCompact_closedBall p (r/2)).measure_ne_top
  refine ⟨V,hV,?_⟩
  have hconst : IntegrableOn (fun _ : Ambient => C) V μ := integrableOn_const hμV
  apply hconst.mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := μ) (s := V) Metric.isClosed_closedBall.measurableSet]
    with q hq
  have hqB : q∈Metric.ball p r := Metric.mem_ball.mpr
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hq) (half_lt_self hr))
  exact hball hqB

def surfaceRatio (d : ℝ) (φ : ℝ→ℂ) (k : Ambient) : ℝ :=
  if liftedEnergy d k=0 then ‖fullDifference φ k‖/‖energyGradient d k‖ else 0

theorem surfaceRatio_nonneg (d : ℝ) (φ : ℝ→ℂ) (k : Ambient) :
    0 ≤ surfaceRatio d φ k := by
  unfold surfaceRatio
  split_ifs <;> positivity

theorem surfaceRatio_measurable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : Continuous φ) : Measurable (surfaceRatio d φ) := by
  have hZ : MeasurableSet {q : Ambient | liftedEnergy d q=0} :=
    (liftedEnergy_continuous hd0 hdU).measurable (measurableSet_singleton 0)
  exact ((fullDifference_continuous hφ).norm.measurable.div
    (energyGradient_continuous hd0 hdU).norm.measurable).piecewise hZ measurable_const

theorem surfaceRatio_local_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period) (k : Ambient) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 k, ‖surfaceRatio d φ q‖≤C := by
  obtain ⟨C,hC,hnear⟩ := full_difference_local_gradient_bound hd0 hdU hφ hp k
  refine ⟨C,hC,?_⟩
  filter_upwards [hnear] with q hq
  rw [Real.norm_eq_abs,abs_of_nonneg (surfaceRatio_nonneg d φ q)]
  by_cases he : liftedEnergy d q=0
  · rw [surfaceRatio,if_pos he]
    by_cases hg : energyGradient d q=0
    · simpa [hg] using hC
    · exact (div_le_iff₀ (norm_pos_iff.mpr hg)).mpr (hq he)
  · simpa only [surfaceRatio,if_neg he] using hC

theorem surfaceRatio_locallyIntegrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period) :
    LocallyIntegrable (surfaceRatio d φ) (zeroSurfaceMeasure d) := by
  letI := zeroSurface_locallyFinite hd0 hdU
  exact locallyIntegrable_of_local_bound (surfaceRatio_measurable hd0 hdU hφ.continuous)
    (surfaceRatio_local_bound hd0 hdU hφ hp)

theorem squareRatio_locallyIntegrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period) :
    LocallyIntegrable (fun k => surfaceRatio d φ k*‖fullDifference φ k‖)
      (zeroSurfaceMeasure d) := by
  letI := zeroSurface_locallyFinite hd0 hdU
  apply locallyIntegrable_of_local_bound
    ((surfaceRatio_measurable hd0 hdU hφ.continuous).mul
      (fullDifference_continuous hφ.continuous).norm.measurable)
  intro k
  obtain ⟨C,hC,hnear⟩ := surfaceRatio_local_bound hd0 hdU hφ hp k
  let M : ℝ := ‖fullDifference φ k‖+1
  have hM : 0≤M := by dsimp [M]; positivity
  have hnearM : ∀ᶠ q in 𝓝 k, ‖fullDifference φ q‖<M :=
    (fullDifference_continuous hφ.continuous).norm.continuousAt.tendsto.eventually_lt_const
      (by dsimp [M]; linarith)
  refine ⟨C*M,mul_nonneg hC hM,?_⟩
  filter_upwards [hnear,hnearM] with q hq hqM
  rw [norm_mul,norm_norm]
  exact mul_le_mul hq hqM.le (norm_nonneg _) hC

theorem regular_area_le_zeroSurface (d : ℝ) :
    (μH[2] : Measure Ambient).restrict (regularSurface d)≤zeroSurfaceMeasure d := by
  apply Measure.restrict_mono_set
  intro k hk
  exact hk.1

theorem coareaWeight_toReal (d : ℝ) (k : Ambient) :
    (coareaWeight d k).toReal=((2*Real.pi)^3*‖energyGradient d k‖)⁻¹ := by
  rw [coareaWeight,ENNReal.toReal_ofReal]
  positivity

/-- The complete squared difference is integrable against the original
regular coarea on every compact real-lift window. -/
theorem full_difference_square_integrableOn {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {K : Set Ambient} (hK : IsCompact K) :
    IntegrableOn (fun k => ‖fullDifference φ k‖^2) K (liftedRegularCoarea d) := by
  have hreg := regularSurface_measurable hd0 hdU
  have hI := (squareRatio_locallyIntegrable hd0 hdU hφ hp).integrableOn_isCompact hK
  have hI' : IntegrableOn (fun k => surfaceRatio d φ k*‖fullDifference φ k‖) K
      ((μH[2] : Measure Ambient).restrict (regularSurface d)) :=
    hI.mono_measure (regular_area_le_zeroSurface d)
  have hJ := hI'.const_mul (((2*Real.pi)^3)⁻¹)
  unfold IntegrableOn liftedRegularCoarea
  rw [restrict_withDensity hK.measurableSet]
  apply (integrable_withDensity_iff (coareaWeight_measurable hd0 hdU)
    (Filter.Eventually.of_forall (fun k => ENNReal.ofReal_lt_top))).mpr
  apply hJ.congr
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem (μ := μH[2]) hreg)] with k hk
  have he : liftedEnergy d k=0 := hk.1
  have hn : ‖energyGradient d k‖≠0 := norm_ne_zero_iff.mpr hk.2
  rw [surfaceRatio,if_pos he,coareaWeight_toReal]
  have hP : (2*Real.pi)^3≠0 := by positivity
  field_simp

end
end Resonance.PinnedFiniteEnergy
