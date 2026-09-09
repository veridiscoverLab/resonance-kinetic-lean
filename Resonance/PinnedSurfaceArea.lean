import Resonance.PinnedCriticalNormalization

/-! Local and compact finite Hausdorff area of the complete pinned energy-zero
set. Critical points are normalized through actual periodic momentum changes. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal NNReal ContDiff
namespace Resonance.PinnedSurfaceArea
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedCriticalNormalization Resonance.PinnedLocalArea
open Resonance.PinnedLegAC

def criticalUngauge (swap : Bool) (n m : ℤ) (k : Ambient) : Ambient :=
  rectangleInverse ((if swap then exchangeIncoming k else k)-latticeShift ![n,m,0])

theorem criticalGauge_ungauge (swap : Bool) (n m : ℤ) (k : Ambient) :
    criticalGauge swap n m (criticalUngauge swap n m k)=k := by
  cases swap <;> simp only [criticalGauge,criticalUngauge,Bool.false_eq_true,
    if_false,if_true,rectangleMap_inverse,sub_add_cancel]
  exact exchangeIncoming_involutive k

theorem criticalUngauge_gauge (swap : Bool) (n m : ℤ) (p : Ambient) :
    criticalUngauge swap n m (criticalGauge swap n m p)=p := by
  cases swap <;> simp only [criticalGauge,criticalUngauge,Bool.false_eq_true,
    if_false,if_true,exchangeIncoming_involutive,add_sub_cancel_right,rectangleInverse_map]

theorem criticalUngauge_continuous (swap : Bool) (n m : ℤ) :
    Continuous (criticalUngauge swap n m) := by
  cases swap <;> unfold criticalUngauge <;> simp only [Bool.false_eq_true,if_false,if_true]
  · exact rectangleInverse.continuous.comp (continuous_id.sub continuous_const)
  · exact rectangleInverse.continuous.comp (exchangeIncoming.continuous.sub continuous_const)

theorem criticalGauge_lipschitz (swap : Bool) (n m : ℤ) :
    ∃ K : ℝ≥0, LipschitzWith K (criticalGauge swap n m) := by
  have h := (isometry_add_right (latticeShift ![n,m,0])).lipschitz.comp rectangleMap.lipschitz
  cases swap
  · exact ⟨_,h⟩
  · exact ⟨_,exchangeIncoming.lipschitz.comp h⟩

theorem criticalUngauge_energy (d : ℝ) (swap : Bool) (n m : ℤ) (k : Ambient) :
    rectangleEnergy d (criticalUngauge swap n m k)=liftedEnergy d k := by
  have h := criticalGauge_energy d swap n m (criticalUngauge swap n m k)
  rw [criticalGauge_ungauge] at h
  exact h.symm

theorem critical_zero_set_locally_finite_area {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ∃ U ∈ 𝓝 k, (μH[2] : Measure Ambient)
      (U ∩ {q | liftedEnergy d q=0})<(∞:ℝ≥0∞) := by
  obtain ⟨swap,n,m,z,v,hk,hgood⟩ :=
    every_critical_point_factor_alternative hd0 hdU he hg
  have hA := rectangle_zero_set_locally_finite_area hd0 hdU
    (WithLp.toLp 2 ![z,0,v]) hgood
  have hA' : ∃ U ∈ 𝓝 (criticalUngauge swap n m k), (μH[2] : Measure Ambient)
      (U ∩ {q | rectangleEnergy d q=0})<(∞:ℝ≥0∞) := by
    rw [←hk,criticalUngauge_gauge]
    exact hA
  obtain ⟨K,hLip⟩ := criticalGauge_lipschitz swap n m
  exact local_area_transport hLip (criticalUngauge_continuous swap n m)
    (criticalGauge_ungauge swap n m) (criticalUngauge_energy d swap n m) k hA'

theorem regular_zero_set_locally_finite_area {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k≠0) :
    ∃ U ∈ 𝓝 k, (μH[2] : Measure Ambient)
      (U ∩ {q | liftedEnergy d q=0})<(∞:ℝ≥0∞) := by
  by_cases hy : velocity d (k 1)=velocity d (k 0+k 1-k 2)
  · by_cases hx : velocity d (k 0)=velocity d (k 0+k 1-k 2)
    · have hz : velocity d (k 2)≠velocity d (k 0+k 1-k 2) := by
        intro hz
        apply hg
        ext i
        fin_cases i <;> simp [energyGradient,hx,hy,hz]
      have hnew : velocity d ((exchangeOutgoing k) 1)≠
          velocity d ((exchangeOutgoing k) 0+(exchangeOutgoing k) 1-(exchangeOutgoing k) 2) := by
        change velocity d (k 1)≠velocity d (k 0+k 1-(k 0+k 1-k 2))
        have hw : k 0+k 1-(k 0+k 1-k 2)=k 2 := by ring
        rw [hw,hy]
        exact hz.symm
      have hA := regular_y_zero_set_finite_area hd0 hdU
        ((energy_exchangeOutgoing d k).trans he) hnew
      exact local_area_transport exchangeOutgoing.lipschitz exchangeOutgoing.continuous
        exchangeOutgoing_involutive (energy_exchangeOutgoing d) k hA
    · have hnew : velocity d ((exchangeIncoming k) 1)≠
          velocity d ((exchangeIncoming k) 0+(exchangeIncoming k) 1-(exchangeIncoming k) 2) := by
        change velocity d (k 0)≠velocity d (k 1+k 0-k 2)
        simpa only [add_comm] using hx
      have hA := regular_y_zero_set_finite_area hd0 hdU
        ((energy_exchangeIncoming d k).trans he) hnew
      exact local_area_transport exchangeIncoming.lipschitz exchangeIncoming.continuous
        exchangeIncoming_involutive (energy_exchangeIncoming d) k hA
  · exact regular_y_zero_set_finite_area hd0 hdU he hy

/-- This local statement covers every point, including all energy-critical
points and all periodic representatives of both trivial pairings. -/
theorem energy_zero_set_locally_finite_area {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (k : Ambient) : ∃ U ∈ 𝓝 k, (μH[2] : Measure Ambient)
      (U ∩ {q | liftedEnergy d q=0})<(∞:ℝ≥0∞) := by
  by_cases he : liftedEnergy d k=0
  · by_cases hg : energyGradient d k=0
    · exact critical_zero_set_locally_finite_area hd0 hdU he hg
    · exact regular_zero_set_locally_finite_area hd0 hdU he hg
  · have hU : {q | liftedEnergy d q≠0} ∈ 𝓝 k :=
      (liftedEnergy_continuous hd0 hdU).continuousAt.eventually_ne he
    refine ⟨_,hU,?_⟩
    have hz : {q | liftedEnergy d q≠0} ∩ {q | liftedEnergy d q=0}=∅ := by
      ext q; simp
    rw [hz,measure_empty]
    exact ENNReal.zero_lt_top

theorem energy_zero_set_compact_finite_area {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {K : Set Ambient} (hK : IsCompact K) :
    (μH[2] : Measure Ambient) (K ∩ {q | liftedEnergy d q=0})<(∞:ℝ≥0∞) := by
  have hZ : MeasurableSet {q : Ambient | liftedEnergy d q=0} :=
    (liftedEnergy_continuous hd0 hdU).measurable (measurableSet_singleton 0)
  have h := hK.measure_lt_top_of_nhdsWithin
    (μ := (μH[2] : Measure Ambient).restrict {q | liftedEnergy d q=0}) ?_
  · simpa only [Measure.restrict_apply' hZ] using h
  · intro k _
    obtain ⟨U,hU,hA⟩ := energy_zero_set_locally_finite_area hd0 hdU k
    exact ⟨U,mem_nhdsWithin_of_mem_nhds hU,by rwa [Measure.restrict_apply' hZ]⟩

end
end Resonance.PinnedSurfaceArea
