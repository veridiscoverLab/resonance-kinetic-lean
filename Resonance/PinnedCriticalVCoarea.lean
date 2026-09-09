import Resonance.PinnedCriticalVAmplitude
import Resonance.PinnedCompleteSourceCutoff
import Resonance.RegularCoareaSupport
import Resonance.CoordinateLevelCoarea

/-! The original complete source in a G-nonzero critical chart: its volume
regularization and its original Euclidean coarea integral both vanish. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedCriticalVCoarea
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalGauge PinnedCriticalCoordinates
open PinnedCriticalFactor PinnedCriticalCancellation CoordinateReplacement PinnedCriticalVAmplitude
open PinnedMeasureNormalization

theorem original_source_integrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=vCoordinates d)
    (hG : ∀p∈e.source,sharedFactor d p≠0)
    (hn : ∀p∈e.source,(fderiv ℝ (coordinateFunction d) p) (unit 2)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source)
    {ρ : ℝ → ℝ} (hm : Measurable ρ) (hρ : Integrable ρ)
    (hpos : ∀q,0≤ρ q) (hmass : ∫q,ρ q=1) :
    Integrable (fun k=>ρ (liftedEnergy d k) • (W k*fullDifference φ k)) := by
  have hA := v_amplitude_regular hd0 hdU hφ hW hK swap n m e hG hn hS
  have hiA := CriticalProductPlaneMollifier.current_integrable hA.1 hA.2 hm hρ hpos hmass
  let B : Ambient → ℂ := fun p=>(e p 1*e p 2) • coefficient d φ W swap n m p
  let r : Ambient → ℝ := fun q=>ρ (-(q 1*q 2))
  have hia : Integrable (fun q=>r q • CoordinateFactoredAmplitude.amplitude 2 (coordinateFunction d) e B q) := by
    have hef := factored_amplitude d φ W swap n m e
    change CoordinateFactoredAmplitude.amplitude 2 (coordinateFunction d) e B=_ at hef
    rw [hef]
    exact hiA.congr (ae_of_all _ (fun q=>smul_comm _ _ _))
  have hi := (CoordinateFactoredAmplitude.source_integrable_iff (F:=coordinateFunction d) 2 e he
    (fun p _=>(coordinateFunction_contDiff hd0 hdU).differentiable (by norm_num) p) hn B r).mp hia
  have hiOn : IntegrableOn (((fun k=>ρ (liftedEnergy d k) •
      (W k*fullDifference φ k)) ∘ gaugeHomeomorph swap n m)) e.source := by
    apply hi.congr
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with p hpS
    dsimp only [B,r,Function.comp_apply]
    rw [complete_factor hφ hp W swap n m (hG p hpS),gauge_energy,he,vCoordinates_energy hd0 hdU]
    congr 2
    ring
  apply (gauge_integrable_iff swap n m).mp
  apply hiOn.integrable_of_forall_notMem_eq_zero
  intro p hp0
  have hz : W (gaugeHomeomorph swap n m p)=0 := by
    by_contra hn0
    exact hp0 (hS (subset_tsupport _ hn0))
  simp [Function.comp_apply,hz]

theorem original_coarea_zero {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    (W : Ambient → ℂ) (swap : Bool) (n m : ℤ) {S : Set Ambient}
    (hG : ∀p∈S,sharedFactor d p≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆S) :
    (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d)=0 := by
  have hzero : ∀ᵐk ∂euclideanLiftedRegularCoarea d,liftedEnergy d k=0 :=
    RegularCoareaSupport.zero_energy_ae
      (CoordinateLevelCoarea.pinned_energy_contDiff_one hd0 hdU).continuous.measurable
      (energyGradient_continuous hd0 hdU).measurable ((2*Real.pi)^3)
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with k hk
  by_cases hw : W k=0
  · simp [hw]
  · let p := (gaugeHomeomorph swap n m).symm k
    have hpk : gaugeHomeomorph swap n m p=k := (gaugeHomeomorph swap n m).apply_symm_apply k
    have hps : p∈S := by
      apply hS
      apply subset_tsupport
      change W (gaugeHomeomorph swap n m p)≠0
      rwa [hpk]
    have he : -p 1*p 2*sharedFactor d p=0 := by
      rw [←PinnedLocalArea.rectangleEnergy_factor hd0 hdU,←gauge_energy d swap n m,hpk]
      exact hk
    have hz : -p 1*p 2=0 := (mul_eq_zero.mp he).resolve_right (hG p hps)
    rw [←hpk,gauge_difference hp,complex_rectangle_factor hφ,hz]
    simp

theorem compact_vchart_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=vCoordinates d)
    (hG : ∀p∈e.source,sharedFactor d p≠0)
    (hn : ∀p∈e.source,(fderiv ℝ (coordinateFunction d) p) (unit 2)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    (∀η,0<η→Integrable (fun k=>ρ η (liftedEnergy d k) • (W k*fullDifference φ k))) ∧
    Integrable (fun k=>W k*fullDifference φ k) (euclideanLiftedRegularCoarea d) ∧
    Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫k,ρ η (liftedEnergy d k) • (W k*fullDifference φ k))
      (𝓝[>]0) (𝓝 (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d)) := by
  refine ⟨fun η hη=>original_source_integrable hd0 hdU hφ hp hW hK
    swap n m e he hG hn hS (hm η hη) (hρ η hη) (hpos η hη) (hmass η hη),
    PinnedCompleteSourceCutoff.complete_source_integrable hd0 hdU hφ hp hW hK,?_⟩
  have hA := v_amplitude_regular hd0 hdU hφ hW hK swap n m e hG hn hS
  have ht := (CriticalProductPlaneMollifier.current_tendsto hA.1 hA.2 ρ hm hρ hpos hmass hs).const_smul
    (((2*Real.pi)^3)⁻¹)
  rw [original_coarea_zero hd0 hdU hφ hp W swap n m hG hS]
  simp only [Complex.real_smul,mul_zero] at ht
  apply ht.congr
  intro η
  rw [source_change hd0 hdU hφ hp W swap n m e he hG hn hS]
  rfl

end
end Resonance.PinnedCriticalVCoarea
