import Resonance.IncomingPairMarginal
import Resonance.WeightedJointMeasure

/-! The actual two-incoming-leg marginal, with the original full quartet
weight and all four sharp flags.  This is the density of the cross term
T₀†T₁ in the common frequency-weighted space. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.IncomingPairDensity
noncomputable section
open ResonantMeasure IncomingPairMarginal

def density (R : ℝ) (w : FourMomenta→ℝ≥0∞) (p : E×E) : ℝ≥0∞ :=
  ENNReal.ofReal (‖p.1-p.2‖/8) * ∫⁻ σ,
    (CoareaNormalization.allFourFlags R).indicator w (incomingQuartet (p,σ)) ∂surface

theorem density_measurable (R : ℝ) {w : FourMomenta→ℝ≥0∞}
    (hw : Measurable w) : Measurable (density R w) := by
  have hm := (hw.indicator (CoareaNormalization.allFourFlags_measurable R)).comp
    incomingQuartet_measurable
  exact (show Measurable (fun p : E×E=>ENNReal.ofReal (‖p.1-p.2‖/8)) by fun_prop).mul
    hm.lintegral_prod_right'

theorem weighted_pair_marginal (R : ℝ) {w : FourMomenta→ℝ≥0∞}
    (hw : Measurable w) :
    Measure.map (fun q : FourMomenta=>(q 0,q 1)) ((pairingMeasure R).withDensity w) =
      ((volume : Measure E).prod volume).withDensity (density R w) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hf01 : Measurable (fun q : FourMomenta=>f (q 0,q 1)) :=
    hf.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  rw [lintegral_map hf ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)),
    lintegral_withDensity_eq_lintegral_mul _ hw hf01,
    lintegral_withDensity_eq_lintegral_mul _ (density_measurable R hw) hf]
  simp only [Pi.mul_apply]
  rw [pairing_incoming_lintegral R _ (hw.mul hf01)]
  have hm : Measurable (fun p : (E×E)×Sphere => ENNReal.ofReal (‖p.1.1-p.1.2‖/8) *
      (CoareaNormalization.allFourFlags R).indicator
        (fun q=>w q*f (q 0,q 1)) (incomingQuartet p)) :=
    (show Measurable (fun p : (E×E)×Sphere=>ENNReal.ofReal (‖p.1.1-p.1.2‖/8))
      by fun_prop).mul
        (((hw.mul hf01).indicator (CoareaNormalization.allFourFlags_measurable R)).comp
          incomingQuartet_measurable)
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro p
  have hi (σ : Sphere) :
      (CoareaNormalization.allFourFlags R).indicator
        (fun q=>w q*f (q 0,q 1)) (incomingQuartet (p,σ)) =
      (CoareaNormalization.allFourFlags R).indicator w (incomingQuartet (p,σ))*f p := by
    by_cases hq : incomingQuartet (p,σ)∈CoareaNormalization.allFourFlags R
    · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq]
      rfl
    · simp only [Set.indicator_of_notMem hq,zero_mul]
  simp_rw [hi]
  have hs : Measurable (fun σ : Sphere=>
      (CoareaNormalization.allFourFlags R).indicator w (incomingQuartet (p,σ))) :=
    ((hw.indicator (CoareaNormalization.allFourFlags_measurable R)).comp
      incomingQuartet_measurable).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_const_mul _ (hs.mul measurable_const),lintegral_mul_const _ hs]
  exact (mul_assoc _ _ _).symm

theorem density_bound (R : ℝ) {w : FourMomenta→ℝ≥0∞} {M : ℝ≥0∞}
    (hb : ∀q∈CoareaNormalization.allFourFlags R,w q≤M) (p : E×E) :
    density R w p ≤ ENNReal.ofReal (‖p.1-p.2‖/8)*M*surface univ := by
  unfold density
  calc
    _ ≤ ENNReal.ofReal (‖p.1-p.2‖/8)*∫⁻ _ : Sphere,M∂surface := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro σ
      dsimp only
      by_cases hq : incomingQuartet (p,σ)∈CoareaNormalization.allFourFlags R
      · rw [Set.indicator_of_mem hq]
        exact hb _ hq
      · rw [Set.indicator_of_notMem hq]
        exact zero_le _
    _ = _ := by rw [lintegral_const]; exact (mul_assoc _ _ _).symm

theorem density_zero_outside (R : ℝ) (w : FourMomenta→ℝ≥0∞) {p : E×E}
    (hp : p∉cube R×ˢcube R) : density R w p=0 := by
  have hz (σ : Sphere) : incomingQuartet (p,σ)∉CoareaNormalization.allFourFlags R := by
    intro hq
    apply hp
    exact ⟨hq 0,hq 1⟩
  simp [density,Set.indicator_of_notMem,hz]

end
end Resonance.IncomingPairDensity
