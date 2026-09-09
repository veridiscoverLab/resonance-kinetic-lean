import Resonance.CrossPairCoordinates
import Resonance.WeightedJointMeasure

/-! The actual incoming--outgoing marginal, with the original full quartet
weight and all four sharp flags.  Its plane integral is the cross term
T₀†T₂ in the same frequency-weighted space. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CrossPairDensity
noncomputable section
open ResonantMeasure CrossPairCoordinates
open PlaneCoarea (E2)

def density (R : ℝ) (w : FourMomenta→ℝ≥0∞) (p : E×E) : ℝ≥0∞ :=
  (1/2 : ℝ≥0∞)*ENNReal.ofReal (‖p.2-p.1‖⁻¹) * ∫⁻ z : E2,
    (CoareaNormalization.allFourFlags R).indicator w (crossQuartet (p,z))

theorem density_measurable (R : ℝ) {w : FourMomenta→ℝ≥0∞}
    (hw : Measurable w) : Measurable (density R w) := by
  have hm := (hw.indicator (CoareaNormalization.allFourFlags_measurable R)).comp
    crossQuartet_measurable
  exact (show Measurable (fun p : E×E=>(1/2 : ℝ≥0∞)*ENNReal.ofReal (‖p.2-p.1‖⁻¹)) by fun_prop).mul
    hm.lintegral_prod_right'

theorem weighted_pair_marginal {R : ℝ} (hR : 0≤R) {w : FourMomenta→ℝ≥0∞}
    (hw : Measurable w) :
    Measure.map (fun q : FourMomenta=>(q 0,q 2)) ((pairingMeasure R).withDensity w) =
      ((volume : Measure E).prod volume).withDensity (density R w) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hf02 : Measurable (fun q : FourMomenta=>f (q 0,q 2)) :=
    hf.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 2))
  rw [lintegral_map hf ((measurable_pi_apply 0).prodMk (measurable_pi_apply 2)),
    lintegral_withDensity_eq_lintegral_mul _ hw hf02,
    lintegral_withDensity_eq_lintegral_mul _ (density_measurable R hw) hf]
  simp only [Pi.mul_apply]
  rw [pairing_cross_lintegral hR _ (hw.mul hf02)]
  have hm : Measurable (fun p : (E×E)×E2 => ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹) *
      (CoareaNormalization.allFourFlags R).indicator
        (fun q=>w q*f (q 0,q 2)) (crossQuartet p)) :=
    (show Measurable (fun p : (E×E)×E2=>ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹))
      by fun_prop).mul
        (((hw.mul hf02).indicator (CoareaNormalization.allFourFlags_measurable R)).comp
          crossQuartet_measurable)
  rw [lintegral_prod _ hm.aemeasurable]
  rw [←lintegral_const_mul _ hm.lintegral_prod_right']
  apply lintegral_congr
  intro p
  have hi (z : E2) :
      (CoareaNormalization.allFourFlags R).indicator
        (fun q=>w q*f (q 0,q 2)) (crossQuartet (p,z)) =
      (CoareaNormalization.allFourFlags R).indicator w (crossQuartet (p,z))*f p := by
    by_cases hq : crossQuartet (p,z)∈CoareaNormalization.allFourFlags R
    · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq]
      rw [crossQuartet_first,crossQuartet_third]
    · simp only [Set.indicator_of_notMem hq,zero_mul]
  simp_rw [hi]
  have hs : Measurable (fun z : E2=>
      (CoareaNormalization.allFourFlags R).indicator w (crossQuartet (p,z))) :=
    ((hw.indicator (CoareaNormalization.allFourFlags_measurable R)).comp
      crossQuartet_measurable).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_const_mul _ (hs.mul measurable_const),lintegral_mul_const _ hs]
  simp only [density,mul_assoc]

theorem density_bound {R : ℝ} (hR : 0≤R) {w : FourMomenta→ℝ≥0∞} {M : ℝ≥0∞}
    (hb : ∀q∈CoareaNormalization.allFourFlags R,w q≤M) (p : E×E) :
    density R w p ≤ (1/2 : ℝ≥0∞)*ENNReal.ofReal (‖p.2-p.1‖⁻¹)*M*
      (volume : Measure E2) (Metric.closedBall 0 (6*R)) := by
  unfold density
  calc
    _ ≤ ((1/2 : ℝ≥0∞)*ENNReal.ofReal (‖p.2-p.1‖⁻¹))*
        ∫⁻ z : E2,(Metric.closedBall 0 (6*R)).indicator (fun _=>M) z := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro z
      dsimp only
      by_cases hq : crossQuartet (p,z)∈CoareaNormalization.allFourFlags R
      · rw [Set.indicator_of_mem hq]
        have hz : z∈Metric.closedBall (0 : E2) (6*R) := by
          have hbound := PlaneGlobal.rectangle_flags_bounds hR p.1 (p.2-p.1)
            (PlaneCoarea.planePoint (PlaneGlobal.direction (p.2-p.1)) z) hq
          have hn : ‖z‖≤6*R := by
            simpa only [PlaneCoarea.planePoint_eq,LinearIsometry.norm_map] using hbound.2.2
          simpa only [Metric.mem_closedBall,dist_zero_right] using hn
        rw [Set.indicator_of_mem hz]
        exact hb _ hq
      · rw [Set.indicator_of_notMem hq]
        exact zero_le _
    _ = _ := by
      rw [lintegral_indicator_const measurableSet_closedBall]
      exact (mul_assoc _ _ _).symm

theorem density_zero_outside (R : ℝ) (w : FourMomenta→ℝ≥0∞) {p : E×E}
    (hp : p∉cube R×ˢcube R) : density R w p=0 := by
  have hz (z : E2) : crossQuartet (p,z)∉CoareaNormalization.allFourFlags R := by
    intro hq
    apply hp
    exact ⟨hq 0,by simpa only [crossQuartet_third] using hq 2⟩
  simp [density,Set.indicator_of_notMem,hz]

end
end Resonance.CrossPairDensity
