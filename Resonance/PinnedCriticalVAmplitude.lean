import Resonance.CoordinateAmplitudeOn
import Resonance.PinnedCriticalGauge
import Resonance.CriticalProductPlaneMollifier

/-! The actual V=vG critical change, retaining the full original source and
its reciprocal Jacobian. Division by G is used only on the actual G-nonzero chart. -/
open Set MeasureTheory
open scoped ContDiff
namespace Resonance.PinnedCriticalVAmplitude
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalGauge PinnedCriticalCoordinates
open PinnedCriticalFactor PinnedCriticalCancellation CoordinateReplacement

def coordinateFunction (d : ℝ) (p : Ambient) : ℝ := p 2*sharedFactor d p

def coefficient (d : ℝ) (φ : ℝ → ℂ) (W : Ambient → ℂ) (swap : Bool) (n m : ℤ)
    (p : Ambient) : ℂ := -(W (gaugeHomeomorph swap n m p)*
      (complexFactor φ p/(sharedFactor d p : ℂ)))

def amplitude (d : ℝ) (φ : ℝ → ℂ) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient) : Ambient → ℂ :=
  CoordinateFactoredAmplitude.amplitude 2 (coordinateFunction d) e (coefficient d φ W swap n m)

theorem coordinateFunction_contDiff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    ContDiff ℝ 1 (coordinateFunction d) :=
  (coordinateProjection 2).contDiff.mul (sharedFactor_contDiff_one hd0 hdU)

theorem coefficient_regular_on {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) {W : Ambient → ℂ}
    (hW : Continuous W) (hK : HasCompactSupport W) (swap : Bool) (n m : ℤ)
    {S : Set Ambient} (hG : ∀p∈S,sharedFactor d p≠0) :
    ContinuousOn (coefficient d φ W swap n m) S ∧
      HasCompactSupport (coefficient d φ W swap n m) := by
  refine ⟨?_, ((gauge_compact_support hK swap n m).mul_right).neg⟩
  exact (((hW.comp (gaugeHomeomorph swap n m).continuous).continuousOn).mul
    ((complexFactor_continuous hφ).continuousOn.div
      (Complex.continuous_ofReal.comp (sharedFactor_contDiff_one hd0 hdU).continuous).continuousOn
      (fun p hp=>Complex.ofReal_ne_zero.mpr (hG p hp)))).neg

theorem coefficient_support (d : ℝ) (φ : ℝ → ℂ) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) :
    tsupport (coefficient d φ W swap n m)⊆tsupport (W ∘ gaugeHomeomorph swap n m) := by
  apply closure_minimal
  · intro p hp
    apply subset_tsupport
    intro hz
    exact hp (by simp [coefficient,show W (gaugeHomeomorph swap n m p)=0 from hz])
  · exact isClosed_tsupport _

theorem complete_factor {d : ℝ} {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hp : Function.Periodic φ period) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) {p : Ambient} (hG : sharedFactor d p≠0) :
    W (gaugeHomeomorph swap n m p)*fullDifference φ (gaugeHomeomorph swap n m p)=
      ((vCoordinates d p) 1*(vCoordinates d p) 2) • coefficient d φ W swap n m p := by
  rw [gauge_difference hp,vCoordinates_difference hφ hG]
  simp only [coefficient,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

theorem v_amplitude_regular {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) {W : Ambient → ℂ}
    (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (hG : ∀p∈e.source,sharedFactor d p≠0)
    (hn : ∀p∈e.source,(fderiv ℝ (coordinateFunction d) p) (unit 2)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source) :
    Continuous (amplitude d φ W swap n m e) ∧ HasCompactSupport (amplitude d φ W swap n m e) :=
  CoordinateAmplitudeOn.amplitude_regular_on 2 e (coordinateFunction_contDiff hd0 hdU).contDiffOn hn
    (coefficient_regular_on hd0 hdU hφ hW hK swap n m hG).1
    (coefficient_regular_on hd0 hdU hφ hW hK swap n m hG).2
    ((coefficient_support d φ W swap n m).trans hS)

theorem factored_amplitude (d : ℝ) (φ : ℝ → ℂ) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient) :
    CoordinateFactoredAmplitude.amplitude 2 (coordinateFunction d) e
      (fun p=>(e p 1*e p 2) • coefficient d φ W swap n m p)=
      fun q=>(q 1*q 2) • amplitude d φ W swap n m e q :=
  CoordinateFactoredAmplitude.factored_formula 2 e _ (fun q=>q 1*q 2)
    (fun p=>e p 1*e p 2) (fun _ _=>rfl)

theorem source_change {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    (W : Ambient → ℂ) (swap : Bool) (n m : ℤ)
    (e : OpenPartialHomeomorph Ambient Ambient) (he : (e : Ambient → Ambient)=vCoordinates d)
    (hG : ∀p∈e.source,sharedFactor d p≠0)
    (hn : ∀p∈e.source,(fderiv ℝ (coordinateFunction d) p) (unit 2)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source) (ρ : ℝ → ℝ) :
    (∫k,ρ (liftedEnergy d k) • (W k*fullDifference φ k))=
      ∫q,CriticalProductPlaneMollifier.current ρ (amplitude d φ W swap n m e) q := by
  rw [←gauge_integral (fun k=>ρ (liftedEnergy d k) • (W k*fullDifference φ k)) swap n m]
  have ho : ∀p∉e.source,ρ (liftedEnergy d (gaugeHomeomorph swap n m p)) •
      (W (gaugeHomeomorph swap n m p)*fullDifference φ (gaugeHomeomorph swap n m p))=0 := by
    intro p hp0
    have hz : W (gaugeHomeomorph swap n m p)=0 := by
      by_contra hn0
      exact hp0 (hS (subset_tsupport _ hn0))
    simp [hz]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero ho]
  have hi := CoordinateFactoredAmplitude.source_integral (F:=coordinateFunction d) 2 e he
    (fun p _=>(coordinateFunction_contDiff hd0 hdU).differentiable (by norm_num) p) hn
    (fun p=>(e p 1*e p 2) • coefficient d φ W swap n m p) (fun q=>ρ (-(q 1*q 2)))
  rw [factored_amplitude] at hi
  calc
    _ = ∫p in e.source,ρ (-(e p 1*e p 2)) • ((e p 1*e p 2) • coefficient d φ W swap n m p) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with p hpS
      rw [complete_factor hφ hp W swap n m (hG p hpS),gauge_energy,he,vCoordinates_energy hd0 hdU]
      congr 2
      ring
    _ = _ := hi.trans (integral_congr_ae (ae_of_all _ (fun q=>smul_comm _ _ _)))

end
end Resonance.PinnedCriticalVAmplitude
