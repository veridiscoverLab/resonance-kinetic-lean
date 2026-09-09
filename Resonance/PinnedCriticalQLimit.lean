import Resonance.PinnedCriticalQAmplitude

/-! Arbitrary-kernel limits for the actual q=G source chart, before the separate
identification of its limiting reading with the original Euclidean coarea. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedCriticalQLimit
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalGauge PinnedCriticalCoordinates
open PinnedCriticalFactor PinnedCriticalCancellation CoordinateReplacement PinnedCriticalQAmplitude

theorem original_source_integrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=qCoordinates d)
    (hn : ∀p∈e.source,(fderiv ℝ (sharedFactor d) p) (unit 0)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source)
    {ρ : ℝ → ℝ} (hm : Measurable ρ) (hρ : Integrable ρ)
    (hpos : ∀q,0≤ρ q) (hmass : ∫q,ρ q=1) :
    Integrable (fun k=>ρ (liftedEnergy d k) • (W k*fullDifference φ k)) := by
  have hGreg := (sharedFactor_contDiff_one hd0 hdU).contDiffOn (s:=e.source)
  have hA := q_amplitude_regular hφ hW hK swap n m e hGreg hn hS
  have hiA := CriticalTripleMollifier.current_integrable hA.1 hA.2 hm hρ hpos hmass
  let B : Ambient → ℂ := fun p=>(p 1*p 2) • coefficient φ W swap n m p
  let r : Ambient → ℝ := fun q=>ρ (-(q 1*q 2)*q 0)
  have hia : Integrable (fun q=>r q • CoordinateFactoredAmplitude.amplitude 0 (sharedFactor d) e B q) := by
    have hef := factored_amplitude φ W swap n m e he
    change CoordinateFactoredAmplitude.amplitude 0 (sharedFactor d) e B=_ at hef
    rw [hef]
    exact hiA.congr (ae_of_all _ (fun q=>smul_comm _ _ _))
  have hi := (CoordinateFactoredAmplitude.source_integrable_iff 0 e he
    (fun p _=>(sharedFactor_contDiff_one hd0 hdU).differentiable (by norm_num) p) hn B r).mp hia
  have hpull : (fun p=>r (e p) • B p)=
      (fun k=>ρ (liftedEnergy d k) • (W k*fullDifference φ k)) ∘ gaugeHomeomorph swap n m := by
    funext p
    dsimp only [B,r,Function.comp_apply]
    rw [complete_factor hφ hp,gauge_energy,he,qCoordinates_energy hd0 hdU]
    congr 2
    ring
  have hiOn : IntegrableOn (((fun k=>ρ (liftedEnergy d k) •
      (W k*fullDifference φ k)) ∘ gaugeHomeomorph swap n m)) e.source :=
    hi.congr (ae_of_all _ (fun p=>congrFun hpull p))
  apply (gauge_integrable_iff swap n m).mp
  apply hiOn.integrable_of_forall_notMem_eq_zero
  intro p hp0
  have hz : W (gaugeHomeomorph swap n m p)=0 := by
    by_contra hn0
    exact hp0 (hS (subset_tsupport _ hn0))
  simp [Function.comp_apply,hz]

theorem original_volume_tendsto {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=qCoordinates d)
    (hn : ∀p∈e.source,(fderiv ℝ (sharedFactor d) p) (unit 0)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    Tendsto (fun η=>∫k,ρ η (liftedEnergy d k) • (W k*fullDifference φ k))
      (𝓝[>]0) (𝓝 (CriticalTripleMollifier.reading (amplitude d φ W swap n m e))) := by
  have hA := q_amplitude_regular hφ hW hK swap n m e
    (sharedFactor_contDiff_one hd0 hdU).contDiffOn hn hS
  have ht := CriticalTripleMollifier.current_tendsto hA.1 hA.2 ρ hm hρ hpos hmass hs
  apply ht.congr
  intro η
  exact (source_change hd0 hdU hφ hp W swap n m e he hn hS (ρ η)).symm

end
end Resonance.PinnedCriticalQLimit
