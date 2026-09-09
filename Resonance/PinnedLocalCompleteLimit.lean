import Resonance.PinnedControlledCritical
import Resonance.PinnedCriticalQCoarea
import Resonance.PinnedCriticalVCoarea

/-! Every original momentum point admits a neighborhood on which the same
complete four-leg source has its original normalized coarea limit. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedLocalCompleteLimit
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalGauge PinnedCriticalCoordinates
open PinnedCriticalFactor PinnedCriticalCancellation CoordinateReplacement
open PinnedMeasureNormalization

def SourceLimit (d : ℝ) (φ : ℝ → ℂ) (ρ : ℝ → ℝ → ℝ) (W : Ambient → ℂ) : Prop :=
  (∀ᶠη in 𝓝[>]0,Integrable (fun k=>ρ η (liftedEnergy d k) • (W k*fullDifference φ k))) ∧
  Integrable (fun k=>W k*fullDifference φ k) (euclideanLiftedRegularCoarea d) ∧
  Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫k,ρ η (liftedEnergy d k) • (W k*fullDifference φ k))
    (𝓝[>]0) (𝓝 (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d))

theorem source_limit_of_all {d : ℝ} {φ : ℝ → ℂ} {ρ : ℝ → ℝ → ℝ} {W : Ambient → ℂ}
    (h : (∀η,0<η→Integrable (fun k=>ρ η (liftedEnergy d k) • (W k*fullDifference φ k))) ∧
      Integrable (fun k=>W k*fullDifference φ k) (euclideanLiftedRegularCoarea d) ∧
      Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫k,ρ η (liftedEnergy d k) • (W k*fullDifference φ k))
        (𝓝[>]0) (𝓝 (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d))) :
    SourceLimit d φ ρ W := by
  refine ⟨?_,h.2⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact h.1 η hη

theorem away_source_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    {δ : ℝ} (hδ : 0<δ) (hS : tsupport W⊆{k|δ < |liftedEnergy d k|})
    (ρ : ℝ → ℝ → ℝ) (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) : SourceLimit d φ ρ W := by
  have hi := PinnedCompleteSourceCutoff.complete_source_integrable hd0 hdU hφ hp hW hK
  have hzero : ∀ᵐk ∂euclideanLiftedRegularCoarea d,liftedEnergy d k=0 :=
    RegularCoareaSupport.zero_energy_ae
      (CoordinateLevelCoarea.pinned_energy_contDiff_one hd0 hdU).continuous.measurable
      (energyGradient_continuous hd0 hdU).measurable ((2*Real.pi)^3)
  have he0 : (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with k hk
    have hw : W k=0 := by
      by_contra hn
      have hh := hS (subset_tsupport W hn)
      simp only [mem_setOf_eq,hk,abs_zero] at hh
      exact (not_lt_of_ge hδ.le) hh
    simp [hw]
  have he : ∀ᶠη in 𝓝[>]0,(fun k=>ρ η (liftedEnergy d k) • (W k*fullDifference φ k))=0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with η hη hsmall
    funext k
    by_cases hw : W k=0
    · simp [hw]
    · have hz : ρ η (liftedEnergy d k)=0 := by
        by_contra hn
        have hu := hs η hη _ hn
        have hl := hS (subset_tsupport W hw)
        exact (not_le_of_gt (hsmall.trans hl)) hu
      simp [hz]
  refine ⟨he.mono (fun η hη=>by
    rw [hη]
    change Integrable (fun _ : Ambient=>(0:ℂ)) (volume : Measure Ambient)
    exact integrable_zero Ambient ℂ volume),hi,?_⟩
  rw [he0]
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with η hη
  rw [hη]
  change (0:ℂ)=((2*Real.pi)^3)⁻¹ • ∫_k : Ambient,(0:ℂ)
  simp only [integral_zero,Complex.real_smul,mul_zero]

theorem every_point_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) (k : Ambient) :
    ∃ U : Set Ambient, IsOpen U ∧ k∈U ∧
      ∀W : Ambient → ℂ, Continuous W → HasCompactSupport W → tsupport W⊆U → SourceLimit d φ ρ W := by
  by_cases hE : liftedEnergy d k=0
  · by_cases hg : energyGradient d k=0
    · obtain ⟨swap,n,m,e,hk,hcase⟩ := PinnedControlledCritical.every_critical_point_controlled hd0 hdU hE hg
      refine ⟨gaugeHomeomorph swap n m '' e.source,
        (gaugeHomeomorph swap n m).isOpenMap _ e.open_source,hk,?_⟩
      intro W hW hK hS
      have hSp : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source := by
        rw [tsupport_comp_eq_preimage]
        intro p hpW
        obtain ⟨q,hq,heq⟩ := hS hpW
        exact (gaugeHomeomorph swap n m).injective heq ▸ hq
      apply source_limit_of_all
      rcases hcase with ⟨he,hn⟩ | ⟨he,hG,hn⟩
      · exact PinnedCriticalQCoarea.compact_qchart_limit hd0 hdU hφ hp hW hK swap n m e he hn hSp
          ρ hm hρ hpos hmass hs
      · exact PinnedCriticalVCoarea.compact_vchart_limit hd0 hdU hφ hp hW hK swap n m e he hG hn hSp
          ρ hm hρ hpos hmass hs
    · refine ⟨{p|energyGradient d p≠0},
        (isClosed_eq (energyGradient_continuous hd0 hdU) continuous_const).isOpen_compl,hg,?_⟩
      intro W hW hK hS
      apply source_limit_of_all
      exact PinnedCompactRegular.compact_regular_limit hd0 hdU
        (hW.mul (fullDifference_continuous hφ.continuous)) hK.mul_right
        (fun p hpB=>hS (tsupport_mul_subset_left hpB)) ρ hρ hpos hmass hs
  · let δ := |liftedEnergy d k|/2
    have hδ : 0<δ := half_pos (abs_pos.mpr hE)
    refine ⟨{p|δ < |liftedEnergy d p|},
      isOpen_lt continuous_const (CoordinateLevelCoarea.pinned_energy_contDiff_one hd0 hdU).continuous.abs,
      (by change |liftedEnergy d k|/2 < |liftedEnergy d k|; exact half_lt_self (abs_pos.mpr hE)),?_⟩
    intro W hW hK hS
    exact away_source_limit hd0 hdU hφ hp hW hK hδ hS ρ hs

end
end Resonance.PinnedLocalCompleteLimit
