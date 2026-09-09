import Resonance.PinnedPeriodicCompactification
import Resonance.PinnedCompactCompleteLimit

/-! Original full-cell regularization: a single compact partition of the
periodic source, the complete four-leg difference, and the original coarea.
Neither the regular nor either critical contribution is deleted. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedPeriodicCompleteLimit
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCompactLocalization
open PinnedMeasureNormalization PinnedCriticalCancellation PeriodicHatPartition PeriodicHatCells

theorem periodic_complete_source_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W)
    (hWp : ∀n k,W (translation n k)=W k)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    (∀ᶠη in 𝓝[>]0,IntegrableOn
      (fun k=>ρ η (liftedEnergy d k) • (W k*fullDifference φ k)) fundamentalCell) ∧
    Integrable (fun k=>W k*fullDifference φ k) (euclideanCellCoarea d) ∧
    Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫k in fundamentalCell,
      ρ η (liftedEnergy d k) • (W k*fullDifference φ k))
      (𝓝[>]0) (𝓝 (∫k,W k*fullDifference φ k ∂euclideanCellCoarea d)) := by
  let B : Ambient → ℂ := fun k=>W k*fullDifference φ k
  have hBp : ∀n k,B (translation n k)=B k := by
    intro n k
    change W (translation n k)*fullDifference φ (translation n k)=W k*fullDifference φ k
    rw [hWp,translation_apply,fullDifference_lattice hp]
  let Wc : Ambient → ℂ := fun k=>weight k • W k
  have hWc : Continuous Wc := by
    simpa only [Wc,Complex.real_smul] using
      (Complex.continuous_ofReal.comp weight_continuous).mul hW
  have hK : HasCompactSupport Wc := weight_hasCompactSupport.smul_right
  obtain ⟨hv,hc,hl⟩ := PinnedCompactCompleteLimit.compact_complete_source_limit
    hd0 hdU hφ hp hWc hK ρ hm hρ hpos hmass hs
  have hc' : Integrable (fun k=>weight k • B k) (euclideanLiftedRegularCoarea d) := by
    simpa only [Wc,B,smul_mul_assoc] using hc
  obtain ⟨hc0,hec⟩ := PinnedPeriodicCompactification.coarea_compactification hd0 hdU B hBp hc'
  have hv' : ∀ᶠη in 𝓝[>]0,
      IntegrableOn (fun k=>ρ η (liftedEnergy d k) • B k) fundamentalCell ∧
      (∫k,ρ η (liftedEnergy d k) • (Wc k*fullDifference φ k))=
        ∫k in fundamentalCell,ρ η (liftedEnergy d k) • B k := by
    filter_upwards [hv] with η hη
    have hper : ∀n k,ρ η (liftedEnergy d (translation n k)) • B (translation n k)=
        ρ η (liftedEnergy d k) • B k := by
      intro n k
      rw [hBp,translation_apply,liftedEnergy_lattice]
    have hnorm : (fun k=>ρ η (liftedEnergy d k) • (Wc k*fullDifference φ k))=
        (fun k=>weight k • (ρ η (liftedEnergy d k) • B k)) := by
      funext k
      simp only [Wc,B,smul_mul_assoc]
      exact smul_comm _ _ _
    have hi : Integrable (fun k=>weight k • (ρ η (liftedEnergy d k) • B k)) := by
      rwa [hnorm] at hη
    obtain ⟨hi0,hei⟩ := PinnedPeriodicCompactification.volume_compactification _ hper hi
    exact ⟨hi0,hnorm ▸ hei⟩
  refine ⟨hv'.mono (fun _ h=>h.1),hc0,?_⟩
  have ht : Tendsto (fun η=>((2*Real.pi)^3)⁻¹ •
      ∫k,ρ η (liftedEnergy d k) • (Wc k*fullDifference φ k))
      (𝓝[>]0) (𝓝 (∫k,B k ∂euclideanCellCoarea d)) := by
    have he : (∫k,Wc k*fullDifference φ k ∂euclideanLiftedRegularCoarea d)=
        ∫k,B k ∂euclideanCellCoarea d := by
      simpa only [Wc,B,smul_mul_assoc] using hec
    rwa [he] at hl
  apply ht.congr'
  filter_upwards [hv'] with η hη
  rw [hη.2]

end
end Resonance.PinnedPeriodicCompleteLimit
