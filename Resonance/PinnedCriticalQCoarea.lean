import Resonance.PinnedCriticalQLimit
import Resonance.PinnedCriticalQCutoff
import Resonance.CriticalTripleReading

/-! Identification of the actual three-factor critical reading with the
original Euclidean coarea. Regular cutoffs are removed in the complete source;
no invariance of surface area under the critical shear is asserted. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedCriticalQCoarea
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalGauge PinnedCriticalCoordinates
open PinnedCriticalFactor PinnedCriticalCancellation CoordinateReplacement
open PinnedCriticalQAmplitude PinnedCriticalQCutoff PinnedCompleteSourceCutoff
open PinnedMeasureNormalization

theorem compact_qchart_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
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
    (∀η,0<η→Integrable (fun k=>ρ η (liftedEnergy d k) • (W k*fullDifference φ k))) ∧
    Integrable (fun k=>W k*fullDifference φ k) (euclideanLiftedRegularCoarea d) ∧
    Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫k,ρ η (liftedEnergy d k) • (W k*fullDifference φ k))
      (𝓝[>]0) (𝓝 (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d)) := by
  refine ⟨fun η hη=>PinnedCriticalQLimit.original_source_integrable hd0 hdU hφ hp hW hK
    swap n m e he hn hS (hm η hη) (hρ η hη) (hpos η hη) (hmass η hη),
    complete_source_integrable hd0 hdU hφ hp hW hK,?_⟩
  let c : ℝ := ((2*Real.pi)^3)⁻¹
  let A := amplitude d φ W swap n m e
  have hA : Continuous A ∧ HasCompactSupport A := q_amplitude_regular hφ hW hK swap n m e
    (sharedFactor_contDiff_one hd0 hdU).contDiffOn hn hS
  have heδ : ∀δ,0<δ→c • CriticalTripleMollifier.reading
      (fun q=>CriticalSourceCutoff.cutoff δ (q 1*q 2) • A q)=
      ∫k,CriticalSourceCutoff.cutoff δ (sharedProduct swap n m k) •
        (W k*fullDifference φ k) ∂euclideanLiftedRegularCoarea d := by
    intro δ hδ
    let Wδ := sourceCutoff W swap n m δ
    have hWδ : Continuous Wδ ∧ HasCompactSupport Wδ := sourceCutoff_regular hW hK swap n m δ
    have hSδ := sourceCutoff_support_chart W swap n m δ hS
    have hq := (PinnedCriticalQLimit.original_volume_tendsto hd0 hdU hφ hp hWδ.1 hWδ.2
      swap n m e he hn hSδ ρ hm hρ hpos hmass hs).const_smul c
    have hr := (PinnedCompactRegular.compact_regular_limit hd0 hdU
      (hWδ.1.mul (fullDifference_continuous hφ.continuous)) hWδ.2.mul_right
      (cutoff_original_gradient hd0 hdU φ W swap n m e hn hS hδ)
      ρ hρ hpos hmass hs).2.2
    have heq := tendsto_nhds_unique hq hr
    change c • CriticalTripleMollifier.reading (amplitude d φ (sourceCutoff W swap n m δ) swap n m e)=_
      at heq
    rw [sourceCutoff_amplitude φ W swap n m e he δ] at heq
    refine heq.trans ?_
    apply integral_congr_ae
    filter_upwards [] with k
    exact smul_mul_assoc _ _ _
  have hread := (CriticalTripleReading.cutoff_reading_tendsto hA.1 hA.2).const_smul c
  have hsource := original_cutoff_tendsto hd0 hdU hφ hp hW hK swap n m
  have hread' : Tendsto (fun δ=>∫k,CriticalSourceCutoff.cutoff δ (sharedProduct swap n m k) •
      (W k*fullDifference φ k) ∂euclideanLiftedRegularCoarea d) (𝓝[>]0)
      (𝓝 (c • CriticalTripleMollifier.reading A)) := by
    apply hread.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact heδ δ hδ
  have heq := tendsto_nhds_unique hread' hsource
  have ht := (PinnedCriticalQLimit.original_volume_tendsto hd0 hdU hφ hp hW hK
    swap n m e he hn hS ρ hm hρ hpos hmass hs).const_smul c
  rw [show c • CriticalTripleMollifier.reading (amplitude d φ W swap n m e)=
    ∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d from heq] at ht
  exact ht

end
end Resonance.PinnedCriticalQCoarea
