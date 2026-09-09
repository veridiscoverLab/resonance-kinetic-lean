import Resonance.FixedEnergyDensity

/-! The full fixed-output coarea law with an actual mark. Its energy-zero
value is the original marked fiber readout, using proved continuity. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedEnergyDensity
noncomputable section
open PlaneCoarea PlaneGlobal CollisionFiber FiberContinuity
open EnergyFiberContinuity FixedEnergyCoarea
set_option maxHeartbeats 1000000

def density (R : ℝ) (Φ : FourMomenta→ℝ) (k : E) (e : ℝ) : ℝ≥0∞ :=
  (1/2:ℝ≥0∞)*∫⁻b:FiberParameters,
    (CoareaNormalization.allFourFlags R).indicator
      (fun q=>ENNReal.ofReal (Φ q)) (planeShell (k,b) e)∂fiberBase

theorem density_measurable (R : ℝ) {Φ : FourMomenta→ℝ} (hΦ : Measurable Φ) (k : E) :
    Measurable (density R Φ k) := by
  have hm : Measurable (fun p:ℝ×FiberParameters=>
      (CoareaNormalization.allFourFlags R).indicator (fun q=>ENNReal.ofReal (Φ q))
        (planeShell (k,p.2) p.1)) :=
    (hΦ.ennreal_ofReal.indicator (CoareaNormalization.allFourFlags_measurable _)).comp
      (planeShell_joint_measurable.comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  exact measurable_const.mul hm.lintegral_prod_right'

theorem density_eq_ofReal {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ)
    (hΦ : Continuous Φ) (hp : ∀q,0≤Φ q) (k : E) (e : ℝ) :
    density R Φ k e=ENNReal.ofReal (energyFiberReadout R Φ k e) := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  have hi := fixed_output_sharp_integrable hR hB Φ hΦ.measurable hbound k e
  have hnonneg : ∀ᵐ b ∂fiberBase,0≤CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e) :=
    ae_of_all _ (fun _=>Set.indicator_nonneg (fun q _=>hp q) _)
  unfold density energyFiberReadout
  rw [ENNReal.ofReal_mul (by norm_num),ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num:(0:ℝ)<2),
    ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
  congr 1
  apply lintegral_congr
  intro b
  by_cases hb:planeShell (k,b) e∈CoareaNormalization.allFourFlags R <;>
    simp [CoareaNormalization.sharpReadout,hb]

theorem density_continuousAt_zero {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ)
    (hΦ : Continuous Φ) (hp : ∀q,0≤Φ q) (k : E) (hk : k∈ResonantMeasure.cube R) :
    ContinuousAt (density R Φ k) 0 := by
  rw [funext (density_eq_ofReal hR Φ hΦ hp k)]
  exact ENNReal.continuous_ofReal.continuousAt.comp
    (energyFiberReadout_continuousAt_zero hR Φ hΦ k hk)

theorem density_zero_original {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ)
    (hΦ : Continuous Φ) (hp : ∀q,0≤Φ q) (k : E) :
    density R Φ k 0=ENNReal.ofReal (fiberReadout R Φ k) := by
  rw [density_eq_ofReal hR Φ hΦ hp,energyFiberReadout_zero R Φ hΦ.measurable]

theorem actual_weighted_energy_density (R : ℝ) (Φ : FourMomenta→ℝ)
    (hΦ : Measurable Φ) (k : E) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻p:E×E,(CoareaNormalization.allFourFlags R).indicator
      (fun q=>ENNReal.ofReal (Φ q)*F (CoareaNormalization.energy q))
        (rectangleFour k p.1 p.2)∂((volume:Measure E).prod volume))=
      ∫⁻e:ℝ,F e*density R Φ k e := by
  have hm : Measurable ((CoareaNormalization.allFourFlags R).indicator
      (fun q=>ENNReal.ofReal (Φ q)*F (CoareaNormalization.energy q))) :=
    (hΦ.ennreal_ofReal.mul (hF.comp (by unfold CoareaNormalization.energy; fun_prop))).indicator
      (CoareaNormalization.allFourFlags_measurable R)
  rw [fixed_output_energy_lintegral k _ hm]
  have hb (e:ℝ) : Measurable (fun b:FiberParameters=>
      (CoareaNormalization.allFourFlags R).indicator (fun q=>ENNReal.ofReal (Φ q))
        (planeShell (k,b) e)) :=
    (hΦ.ennreal_ofReal.indicator (CoareaNormalization.allFourFlags_measurable _)).comp
      (fixed_output_shell_measurable k e)
  have he (e:ℝ) : (∫⁻b:FiberParameters,(CoareaNormalization.allFourFlags R).indicator
      (fun q=>ENNReal.ofReal (Φ q)*F (CoareaNormalization.energy q)) (planeShell (k,b) e)∂fiberBase)=
      F e*∫⁻b:FiberParameters,(CoareaNormalization.allFourFlags R).indicator
        (fun q=>ENNReal.ofReal (Φ q)) (planeShell (k,b) e)∂fiberBase := by
    rw [←lintegral_const_mul _ (hb e)]
    apply lintegral_congr
    intro b
    by_cases hf:planeShell (k,b) e∈CoareaNormalization.allFourFlags R <;>
      simp [hf,planeShell_energy,mul_comm]
  simp_rw [he]
  have hout : Measurable (fun e:ℝ=>F e*∫⁻b:FiberParameters,
      (CoareaNormalization.allFourFlags R).indicator (fun q=>ENNReal.ofReal (Φ q))
        (planeShell (k,b) e)∂fiberBase) := by
    have hh : Measurable (fun p:ℝ×FiberParameters=>
        (CoareaNormalization.allFourFlags R).indicator (fun q=>ENNReal.ofReal (Φ q))
          (planeShell (k,p.2) p.1)) :=
      (hΦ.ennreal_ofReal.indicator (CoareaNormalization.allFourFlags_measurable _)).comp
        (planeShell_joint_measurable.comp
          (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
    exact hF.mul hh.lintegral_prod_right'
  rw [←lintegral_const_mul _ hout]
  apply lintegral_congr
  intro e
  unfold density
  ring

end
end Resonance.MarkedEnergyDensity
