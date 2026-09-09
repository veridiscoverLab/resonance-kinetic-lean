import Resonance.MarkedEnergyDensity
import Resonance.CubeFrequencyReflection

/-! Exact simultaneous cube isometries of the original marked fiber.
All four legs and the output are transported together. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.MarkedFiberIsometry
noncomputable section
open PlaneCoarea CubeFrequencyReflection MarkedEnergyDensity CollisionFrequencyConvolution
set_option maxHeartbeats 1200000

def pullback (J : E≃ₗᵢ[ℝ]E) (Φ : FourMomenta→ℝ) (q : FourMomenta) : ℝ :=
  Φ (fun l=>J (q l))

theorem pullback_continuous (J : E≃ₗᵢ[ℝ]E) {Φ : FourMomenta→ℝ} (hΦ : Continuous Φ) :
    Continuous (pullback J Φ) := by
  unfold pullback
  apply hΦ.comp
  exact continuous_pi (fun l=>J.continuous.comp (continuous_apply l))

theorem actual_energy_lintegral_isometry (R : ℝ) (J : E≃ₗᵢ[ℝ]E)
    (hJ : ∀x:E,J x∈ResonantMeasure.cube R↔x∈ResonantMeasure.cube R)
    {Φ : FourMomenta→ℝ} (hΦ : Continuous Φ) (k : E) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻e:ℝ,F e*density R Φ (J k) e)=∫⁻e:ℝ,F e*density R (pullback J Φ) k e := by
  classical
  rw [←actual_weighted_energy_density R Φ hΦ.measurable (J k) F hF,
    ←actual_weighted_energy_density R (pullback J Φ) (pullback_continuous J hΦ).measurable k F hF]
  let G : E×E→ℝ≥0∞ := fun p=>(CoareaNormalization.allFourFlags R).indicator
    (fun q=>ENNReal.ofReal (Φ q)*F (CoareaNormalization.energy q)) (rectangleFour (J k) p.1 p.2)
  have hG : Measurable G :=
    ((hΦ.measurable.ennreal_ofReal.mul (hF.comp (by unfold CoareaNormalization.energy; fun_prop))).indicator
      (CoareaNormalization.allFourFlags_measurable _)).comp
        (rectangleFour_continuous.measurable.comp
          (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  have hpres : MeasurePreserving (fun p:E×E=>(J p.1,J p.2)) volume volume :=
    J.measurePreserving.prod J.measurePreserving
  have he := lintegral_map (μ:=(volume:Measure (E×E))) hG hpres.measurable
  rw [hpres.map_eq] at he
  change (∫⁻p:E×E,G p)=_
  rw [he]
  apply lintegral_congr
  intro p
  have hflags : rectangleFour (J k) (J p.1) (J p.2)∈CoareaNormalization.allFourFlags R↔
      rectangleFour k p.1 p.2∈CoareaNormalization.allFourFlags R := by
    change (∀l,rectangleFour (J k) (J p.1) (J p.2) l∈ResonantMeasure.cube R)↔
      (∀l,rectangleFour k p.1 p.2 l∈ResonantMeasure.cube R)
    rw [rectangleFour_isometry]
    exact forall_congr' (fun l=>hJ _)
  dsimp only [G]
  by_cases hp:rectangleFour k p.1 p.2∈CoareaNormalization.allFourFlags R
  · rw [indicator_of_mem hp,indicator_of_mem (hflags.mpr hp)]
    rw [rectangleFour_energy,rectangleFour_energy,J.inner_map_map,rectangleFour_isometry]
    rfl
  · rw [indicator_of_notMem hp,indicator_of_notMem (fun h=>hp (hflags.mp h))]

theorem original_marked_fiber_isometry {R : ℝ} (hR : 0≤R) (J : E≃ₗᵢ[ℝ]E)
    (hJ : ∀x:E,J x∈ResonantMeasure.cube R↔x∈ResonantMeasure.cube R)
    {Φ : FourMomenta→ℝ} (hΦ : Continuous Φ) (hp : ∀q,0≤Φ q)
    (k : E) (hk : k∈ResonantMeasure.cube R) :
    FiberContinuity.fiberReadout R Φ (J k)=FiberContinuity.fiberReadout R (pullback J Φ) k := by
  have hm := density_measurable R hΦ.measurable (J k)
  have hn := density_measurable R (pullback_continuous J hΦ).measurable k
  have hae : density R Φ (J k)=ᵐ[(volume:Measure ℝ)]density R (pullback J Φ) k := by
    apply (withDensity_eq_iff_of_sigmaFinite hm.aemeasurable hn.aemeasurable).mp
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul _ hm hF,lintegral_withDensity_eq_lintegral_mul _ hn hF]
    simpa only [mul_comm] using actual_energy_lintegral_isometry R J hJ hΦ k F hF
  have h := continuousAt_zero_eq_of_ae_eq hae
    (density_continuousAt_zero hR Φ hΦ hp (J k) ((hJ k).mpr hk))
    (density_continuousAt_zero hR (pullback J Φ) (pullback_continuous J hΦ) (fun q=>hp _) k hk)
  rw [density_zero_original hR Φ hΦ hp,density_zero_original hR (pullback J Φ)
    (pullback_continuous J hΦ) (fun q=>hp _)] at h
  have hreal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (show 0≤FiberContinuity.fiberReadout R Φ (J k) from
    integral_nonneg hp),ENNReal.toReal_ofReal (show 0≤FiberContinuity.fiberReadout R (pullback J Φ) k from
    integral_nonneg (fun q=>hp _))] using hreal

end
end Resonance.MarkedFiberIsometry
