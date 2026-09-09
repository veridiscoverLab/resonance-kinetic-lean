import Resonance.CrossPairDensity
import Resonance.CollisionFiber

/-! Pointwise disintegration of the actual fixed-output fiber over its third
leg.  This is a fixed-k identity, not an upgrade of an almost-everywhere
disintegration.  The full quartet and every sharp flag are retained. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.FixedCrossRow
noncomputable section
set_option maxHeartbeats 600000
open ResonantMeasure PlaneGlobal CollisionFiber CrossPairMarginal
  CrossPairCoordinates
open PlaneCoarea (E2 rayMeasure)

theorem fiberBase_from_rayMeasure : fiberBase =
    (rayMeasure.prod (volume : Measure E2)).withDensity
      (fun b : FiberParameters => ENNReal.ofReal ((b.1.2 : ℝ)⁻¹)) := by
  rw [fiberBase, rayOne_from_rayMeasure, prod_withDensity_left (by fun_prop)]

theorem fixed_polar_lintegral (k : E) (Φ : FourMomenta → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ b, Φ (fiberFour k b) ∂fiberBase) =
      ∫⁻ p : E×E2, ENNReal.ofReal (‖p.1‖⁻¹) *
        Φ (relativeQuartet (k,p)) ∂((volume : Measure E).prod volume) := by
  rw [fiberBase_from_rayMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun b : FiberParameters =>
    ENNReal.ofReal ((b.1.2 : ℝ)⁻¹)) (g := fun b => Φ (fiberFour k b))
    (by fun_prop) (hΦ.comp (fiberFour_measurable k))]
  have hm : Measurable (fun p : E×E2 => ENNReal.ofReal (‖p.1‖⁻¹) *
      Φ (relativeQuartet (k,p))) :=
    (show Measurable (fun p : E×E2 => ENNReal.ofReal (‖p.1‖⁻¹)) by fun_prop).mul (hΦ.comp (relativeQuartet_measurable.comp
      (measurable_const.prodMk measurable_id)))
  have ht := (PolarCoordinates.polarVector_preserves_volume.prod
    (MeasurePreserving.id (volume : Measure E2))).lintegral_comp hm
  apply Eq.trans _ ht
  apply lintegral_congr
  intro b
  have hn : ‖PolarCoordinates.polarVector b.1‖ = (b.1.2 : ℝ) := by
    simpa only [cartesianPlane] using cartesianPlane_norm (k,b)
  have hq : relativeQuartet (k,(PolarCoordinates.polarVector b.1,b.2)) =
      fiberFour k b := by
    exact relativeQuartet_cartesianPlane (k,b)
  simp only [Pi.mul_apply, Prod.map, id_eq, hn, hq]

theorem fixed_cross_lintegral (k : E) (Φ : FourMomenta → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ b, Φ (fiberFour k b) ∂fiberBase) =
      ∫⁻ p : E, ENNReal.ofReal (‖p-k‖⁻¹) *
        ∫⁻ z : E2, Φ (crossQuartet ((k,p),z)) := by
  rw [fixed_polar_lintegral k Φ hΦ]
  have hm : Measurable (fun p : E×E2 => ENNReal.ofReal (‖p.1‖⁻¹) *
      Φ (relativeQuartet (k,p))) :=
    (show Measurable (fun p : E×E2 => ENNReal.ofReal (‖p.1‖⁻¹)) by fun_prop).mul (hΦ.comp (relativeQuartet_measurable.comp
      (measurable_const.prodMk measurable_id)))
  rw [lintegral_prod _ hm.aemeasurable]
  have he (p : E) : (∫⁻ z : E2, ENNReal.ofReal (‖p‖⁻¹) *
      Φ (relativeQuartet (k,p,z))) = ENNReal.ofReal (‖p‖⁻¹) *
      ∫⁻ z : E2, Φ (relativeQuartet (k,p,z)) := by
    apply lintegral_const_mul
    exact hΦ.comp (relativeQuartet_measurable.comp (by fun_prop))
  simp_rw [he]
  have ht := lintegral_sub_right_eq_self (μ := (volume : Measure E))
    (fun p : E => ENNReal.ofReal (‖p‖⁻¹) *
      ∫⁻ z : E2, Φ (relativeQuartet (k,p,z))) k
  simpa only [crossQuartet] using ht.symm

theorem fiber_cross_lintegral (R : ℝ) (k : E) (Φ : FourMomenta → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ q, Φ q ∂fiberMeasure R k) =
      ∫⁻ p : E, CrossPairDensity.density R Φ (k,p) := by
  let ψ := (CoareaNormalization.allFourFlags R).indicator Φ
  have hψ : Measurable ψ := hΦ.indicator (CoareaNormalization.allFourFlags_measurable R)
  have hi : (fiberAllowed R k).indicator (fun b => Φ (fiberFour k b)) =
      fun b => ψ (fiberFour k b) := by
    funext b
    by_cases hb : b ∈ fiberAllowed R k
    · simp only [Set.indicator_of_mem hb, ψ,
        Set.indicator_of_mem (show fiberFour k b ∈ CoareaNormalization.allFourFlags R from hb)]
    · simp only [Set.indicator_of_notMem hb, ψ,
        Set.indicator_of_notMem (show fiberFour k b ∉ CoareaNormalization.allFourFlags R from hb)]
  rw [fiberMeasure, lintegral_smul_measure, smul_eq_mul,
    lintegral_map hΦ (fiberFour_measurable k),
    ← lintegral_indicator (fiberAllowed_measurable R k), hi,
    fixed_cross_lintegral k ψ hψ]
  rw [← lintegral_const_mul' (1/2 : ℝ≥0∞) _ (by norm_num)]
  apply lintegral_congr
  intro p
  simp only [CrossPairDensity.density, ψ, mul_assoc]

theorem weighted_fixed_cross_row (R : ℝ) (k : E)
    (w : FourMomenta → ℝ≥0∞) (hw : Measurable w)
    (h : E → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ q, w q * h (q 2) ∂fiberMeasure R k) =
      ∫⁻ p : E, CrossPairDensity.density R w (k,p) * h p := by
  rw [fiber_cross_lintegral R k (fun q => w q * h (q 2))
    (hw.mul (hh.comp (measurable_pi_apply 2)))]
  apply lintegral_congr
  intro p
  have hi (z : E2) :
      (CoareaNormalization.allFourFlags R).indicator
        (fun q => w q * h (q 2)) (crossQuartet ((k,p),z)) =
      (CoareaNormalization.allFourFlags R).indicator w
        (crossQuartet ((k,p),z)) * h p := by
    by_cases hq : crossQuartet ((k,p),z) ∈ CoareaNormalization.allFourFlags R
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, crossQuartet_third]
    · simp only [Set.indicator_of_notMem hq, zero_mul]
  simp only [CrossPairDensity.density]
  simp_rw [hi]
  have hm : Measurable (fun z : E2 => (CoareaNormalization.allFourFlags R).indicator w
      (crossQuartet ((k,p),z))) :=
    (hw.indicator (CoareaNormalization.allFourFlags_measurable R)).comp
      (crossQuartet_measurable.comp (measurable_const.prodMk measurable_id))
  rw [lintegral_mul_const _ hm]
  exact (mul_assoc _ _ _).symm

end
end Resonance.FixedCrossRow
