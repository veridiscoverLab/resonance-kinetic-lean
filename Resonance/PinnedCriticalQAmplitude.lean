import Resonance.CoordinateFactoredAmplitude
import Resonance.PinnedCriticalGauge
import Resonance.CriticalTripleMollifier

/-! The complete original pinned source in the actual q=G chart. The source
amplitude contains its true inverse Jacobian and the full four-leg factor. -/
open Set MeasureTheory
open scoped ContDiff
namespace Resonance.PinnedCriticalQAmplitude
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalGauge PinnedCriticalCoordinates
open PinnedCriticalFactor PinnedCriticalCancellation CoordinateReplacement

def coefficient (φ : ℝ → ℂ) (W : Ambient → ℂ) (swap : Bool) (n m : ℤ)
    (p : Ambient) : ℂ := -(W (gaugeHomeomorph swap n m p)*complexFactor φ p)

def amplitude (d : ℝ) (φ : ℝ → ℂ) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient) : Ambient → ℂ :=
  CoordinateFactoredAmplitude.amplitude 0 (sharedFactor d) e (coefficient φ W swap n m)

theorem coefficient_regular {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) :
    Continuous (coefficient φ W swap n m) ∧ HasCompactSupport (coefficient φ W swap n m) := by
  exact ⟨((hW.comp (gaugeHomeomorph swap n m).continuous).mul (complexFactor_continuous hφ)).neg,
    ((gauge_compact_support hK swap n m).mul_right).neg⟩

theorem coefficient_support (φ : ℝ → ℂ) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) :
    tsupport (coefficient φ W swap n m)⊆tsupport (W ∘ gaugeHomeomorph swap n m) := by
  apply closure_minimal
  · intro p hp
    apply subset_tsupport
    intro hz
    exact hp (by simpa only [Function.comp_apply] using
      (show coefficient φ W swap n m p=0 by simp [coefficient,show W (gaugeHomeomorph swap n m p)=0 from hz]))
  · exact isClosed_tsupport _

theorem complete_factor {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hp : Function.Periodic φ period) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) (p : Ambient) :
    W (gaugeHomeomorph swap n m p)*fullDifference φ (gaugeHomeomorph swap n m p)=
      (p 1*p 2) • coefficient φ W swap n m p := by
  rw [gauge_difference hp,complex_rectangle_factor hφ]
  simp only [coefficient,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

theorem q_amplitude_regular {d : ℝ} {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (hG : ContDiffOn ℝ 1 (sharedFactor d) e.source)
    (hn : ∀p∈e.source,(fderiv ℝ (sharedFactor d) p) (unit 0)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source) :
    Continuous (amplitude d φ W swap n m e) ∧ HasCompactSupport (amplitude d φ W swap n m e) :=
  CoordinateFactoredAmplitude.amplitude_regular 0 e hG hn
    (coefficient_regular hφ hW hK swap n m).1 (coefficient_regular hφ hW hK swap n m).2
    ((coefficient_support φ W swap n m).trans hS)

theorem factored_amplitude {d : ℝ} (φ : ℝ → ℂ) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=qCoordinates d) :
    CoordinateFactoredAmplitude.amplitude 0 (sharedFactor d) e
      (fun p=>(p 1*p 2) • coefficient φ W swap n m p)=
      fun q=>(q 1*q 2) • amplitude d φ W swap n m e q := by
  apply CoordinateFactoredAmplitude.factored_formula
  intro p _
  rw [he]
  simp [qCoordinates,replace_apply,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide]

theorem source_change {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    (W : Ambient → ℂ) (swap : Bool) (n m : ℤ)
    (e : OpenPartialHomeomorph Ambient Ambient) (he : (e : Ambient → Ambient)=qCoordinates d)
    (hn : ∀p∈e.source,(fderiv ℝ (sharedFactor d) p) (unit 0)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source) (ρ : ℝ → ℝ) :
    (∫k,ρ (liftedEnergy d k) • (W k*fullDifference φ k))=
      ∫q,CriticalTripleMollifier.current ρ (amplitude d φ W swap n m e) q := by
  rw [←gauge_integral (fun k=>ρ (liftedEnergy d k) • (W k*fullDifference φ k)) swap n m]
  have ho : ∀p∉e.source,ρ (liftedEnergy d (gaugeHomeomorph swap n m p)) •
      (W (gaugeHomeomorph swap n m p)*fullDifference φ (gaugeHomeomorph swap n m p))=0 := by
    intro p hp0
    have hz : W (gaugeHomeomorph swap n m p)=0 := by
      by_contra hn0
      exact hp0 (hS (subset_tsupport _ hn0))
    simp [hz]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero ho]
  have hi := CoordinateFactoredAmplitude.source_integral 0 e he
    (fun p _=>(sharedFactor_contDiff_one hd0 hdU).differentiable (by norm_num) p) hn
    (fun p=>(p 1*p 2) • coefficient φ W swap n m p)
    (fun q=>ρ (-(q 1*q 2)*q 0))
  rw [factored_amplitude φ W swap n m e he] at hi
  have hel : ∀p,ρ (-(e p 1*e p 2)*e p 0) • ((p 1*p 2) • coefficient φ W swap n m p)=
      ρ (liftedEnergy d (gaugeHomeomorph swap n m p)) •
        (W (gaugeHomeomorph swap n m p)*fullDifference φ (gaugeHomeomorph swap n m p)) := by
    intro p
    rw [complete_factor hφ hp,gauge_energy,he,qCoordinates_energy hd0 hdU]
    congr 2
    ring
  calc
    _ = ∫p in e.source,ρ (-(e p 1*e p 2)*e p 0) • ((p 1*p 2) • coefficient φ W swap n m p) :=
      integral_congr_ae (ae_of_all _ (fun p=>(hel p).symm))
    _ = _ := hi.trans (integral_congr_ae (ae_of_all _ (fun q=>smul_comm _ _ _)))

end
end Resonance.PinnedCriticalQAmplitude
