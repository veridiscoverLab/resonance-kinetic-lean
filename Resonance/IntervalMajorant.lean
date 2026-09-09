import Resonance.MarkedCoordinateSymmetry

/-! Explicit continuous majorants turn original marked-fiber bounds
into bounds for the actual measurable strip events. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.IntervalMajorant
noncomputable section
open PlaneCoarea CollisionFiber CollisionFrequency FiberContinuity
set_option maxHeartbeats 1000000

def clamp (x : ℝ) : ℝ := min 1 (max 0 x)

theorem clamp_bounds (x : ℝ) : 0≤clamp x ∧ clamp x≤1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem clamp_zero {x : ℝ} (hx : x≤0) : clamp x=0 := by simp [clamp,max_eq_left hx]

theorem clamp_one {x : ℝ} (hx : 1≤x) : clamp x=1 :=
  min_eq_left (hx.trans (le_max_right _ _))

def majorant (a b ε s : ℝ) : ℝ :=
  clamp ((s-a+ε)/ε)*clamp ((b+ε-s)/ε)

theorem majorant_continuous (a b ε : ℝ) : Continuous (majorant a b ε) := by
  unfold majorant clamp
  fun_prop

theorem majorant_bounds (a b ε s : ℝ) : 0 ≤ majorant a b ε s ∧ majorant a b ε s≤1 := by
  constructor
  · exact mul_nonneg (clamp_bounds _).1 (clamp_bounds _).1
  · exact (mul_le_mul (clamp_bounds _).2 (clamp_bounds _).2 (clamp_bounds _).1 (by norm_num)).trans_eq
      (mul_one 1)

theorem majorant_one {a b ε s : ℝ} (hε : 0<ε) (hs : s∈Icc a b) : majorant a b ε s=1 := by
  have h1 : 1≤(s-a+ε)/ε := (le_div_iff₀ hε).mpr (by linarith [hs.1])
  have h2 : 1≤(b+ε-s)/ε := (le_div_iff₀ hε).mpr (by linarith [hs.2])
  rw [majorant,clamp_one h1,clamp_one h2,mul_one]

theorem majorant_support {a b ε s : ℝ} (hε : 0<ε) (hs : s∉Icc (a-ε) (b+ε)) :
    majorant a b ε s=0 := by
  unfold majorant
  by_cases ha:s<a-ε
  · rw [clamp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le),zero_mul]
  · have hb : b+ε<s := lt_of_not_ge (fun h=>hs ⟨le_of_not_gt ha,h⟩)
    have hz : clamp ((b+ε-s)/ε)=0 :=
      clamp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
    rw [hz,mul_zero]

theorem actual_fiber_measure_majorant {R : ℝ} (hR : 0≤R) (k : E)
    {S : Set FourMomenta} (hS : MeasurableSet S) {Φ : FourMomenta→ℝ}
    (hΦ : Measurable Φ) (hp : ∀q,0≤Φ q) (hb : ∀q,Φ q≤1)
    (hmajor : ∀q∈S,1≤Φ q) :
    fiberMeasure R k S≤ENNReal.ofReal (fiberReadout R Φ k) := by
  letI : IsFiniteMeasure (fiberMeasure R k) := ⟨geometricFrequency_mass_finite hR k⟩
  have hi : Integrable Φ (fiberMeasure R k) := Integrable.of_bound hΦ.aestronglyMeasurable 1
    (ae_of_all _ (fun q=>by rw [Real.norm_eq_abs,abs_of_nonneg (hp q)]; exact hb q))
  rw [fiberReadout,ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp)]
  have hpoint (q : FourMomenta) : S.indicator (fun _=>(1:ℝ≥0∞)) q≤ENNReal.ofReal (Φ q) := by
    by_cases hq:q∈S
    · rw [indicator_of_mem hq]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hmajor q hq)
    · rw [indicator_of_notMem hq]
      exact zero_le _
  have h := lintegral_mono (μ:=fiberMeasure R k) hpoint
  simpa only [lintegral_indicator hS,lintegral_const,one_mul,Measure.restrict_apply_univ] using h

end
end Resonance.IntervalMajorant
