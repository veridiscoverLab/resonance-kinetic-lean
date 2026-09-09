import Resonance.FixedEnergyCoarea

/-! The density of the actual fixed-output energy pushforward.  Its
continuous representative at energy zero is the original fiber mass. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.FixedEnergyDensity
noncomputable section
set_option maxHeartbeats 800000
open Resonance.PlaneCoarea Resonance.PlaneGlobal Resonance.CollisionFiber
open Resonance.EnergyFiberContinuity Resonance.FixedEnergyCoarea

def fiberDensity (R:ℝ) (k:E) (e:ℝ) : ℝ≥0∞ := ENNReal.ofReal (energyFiberMass R k e)

theorem fiberDensity_lintegral {R:ℝ} (hR:0≤R) (k:E) (e:ℝ) :
    fiberDensity R k e=(1/2:ℝ≥0∞)*∫⁻b:FiberParameters,
      (CoareaNormalization.allFourFlags R).indicator (fun _=>1) (planeShell (k,b) e) ∂fiberBase := by
  have hi := fixed_output_sharp_integrable hR (by norm_num : (0:ℝ)≤1)
    (fun _:FourMomenta=>1) measurable_const (by intro q hq; norm_num) k e
  have hpos : 0≤ᵐ[fiberBase] (fun b:FiberParameters=>
      CoareaNormalization.sharpReadout R (fun _=>1) (planeShell (k,b) e)) := by
    apply ae_of_all
    intro b
    exact Set.indicator_nonneg (fun _ _=>by norm_num) _
  unfold fiberDensity energyFiberMass energyFiberReadout
  rw [ENNReal.ofReal_mul (by norm_num),ofReal_integral_eq_lintegral_ofReal hi hpos]
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
  congr 1
  apply lintegral_congr
  intro b
  by_cases hb:planeShell (k,b) e∈CoareaNormalization.allFourFlags R
  · simp [CoareaNormalization.sharpReadout,hb]
  · simp [CoareaNormalization.sharpReadout,hb]

theorem fiberDensity_measurable {R:ℝ} (hR:0≤R) (k:E) : Measurable (fiberDensity R k) := by
  have he : fiberDensity R k=fun e=>(1/2:ℝ≥0∞)*∫⁻b:FiberParameters,
      (CoareaNormalization.allFourFlags R).indicator (fun _=>1) (planeShell (k,b) e) ∂fiberBase :=
    funext (fiberDensity_lintegral hR k)
  rw [he]
  have hm : Measurable (fun p:ℝ×FiberParameters=>
      (CoareaNormalization.allFourFlags R).indicator (fun _:FourMomenta=> (1:ℝ≥0∞))
        (planeShell (k,p.2) p.1)) :=
    (measurable_const.indicator (CoareaNormalization.allFourFlags_measurable _)).comp
      (planeShell_joint_measurable.comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  exact measurable_const.mul hm.lintegral_prod_right'

theorem fiberDensity_continuousAt_zero {R:ℝ} (hR:0≤R) (k:E)
    (hk:k∈ResonantMeasure.cube R) : ContinuousAt (fiberDensity R k) 0 :=
  ENNReal.continuous_ofReal.continuousAt.comp (energyFiberMass_continuousAt_zero hR k hk)

theorem fiberDensity_zero (R:ℝ) (k:E) : fiberDensity R k 0=
    ENNReal.ofReal (CollisionFrequency.geometricFrequency R k) := by
  rw [fiberDensity,energyFiberMass_zero]

theorem sharp_energy_density {R:ℝ} (hR:0≤R) (k:E)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻p:E×E,(CoareaNormalization.allFourFlags R).indicator
      (fun q:FourMomenta=>F (CoareaNormalization.energy q)) (rectangleFour k p.1 p.2)
      ∂((volume:Measure E).prod volume))=
      ∫⁻e:ℝ,F e*fiberDensity R k e := by
  have hm : Measurable ((CoareaNormalization.allFourFlags R).indicator
      (fun q:FourMomenta=>F (CoareaNormalization.energy q))) :=
    (hF.comp (by unfold CoareaNormalization.energy; fun_prop)).indicator
      (CoareaNormalization.allFourFlags_measurable R)
  rw [fixed_output_energy_lintegral k _ hm]
  have hb (e:ℝ) : Measurable (fun b:FiberParameters=>
      (CoareaNormalization.allFourFlags R).indicator (fun _:FourMomenta=>(1:ℝ≥0∞))
        (planeShell (k,b) e)) :=
    (measurable_const.indicator (CoareaNormalization.allFourFlags_measurable _)).comp
      (fixed_output_shell_measurable k e)
  have he (e:ℝ) : (∫⁻b:FiberParameters,
      (CoareaNormalization.allFourFlags R).indicator
        (fun q:FourMomenta=>F (CoareaNormalization.energy q)) (planeShell (k,b) e) ∂fiberBase)=
      F e*∫⁻b:FiberParameters,(CoareaNormalization.allFourFlags R).indicator
        (fun _:FourMomenta=>(1:ℝ≥0∞)) (planeShell (k,b) e) ∂fiberBase := by
    rw [←lintegral_const_mul _ (hb e)]
    apply lintegral_congr
    intro b
    by_cases hf:planeShell (k,b) e∈CoareaNormalization.allFourFlags R
    · simp [hf,planeShell_energy]
    · simp [hf]
  simp_rw [he]
  have hout : Measurable (fun e:ℝ=>F e*∫⁻b:FiberParameters,
      (CoareaNormalization.allFourFlags R).indicator
        (fun _:FourMomenta=>(1:ℝ≥0∞)) (planeShell (k,b) e) ∂fiberBase) := by
    have h : Measurable (fun p:ℝ×FiberParameters=>
        (CoareaNormalization.allFourFlags R).indicator (fun _:FourMomenta=>(1:ℝ≥0∞))
          (planeShell (k,p.2) p.1)) :=
      (measurable_const.indicator (CoareaNormalization.allFourFlags_measurable _)).comp
        (planeShell_joint_measurable.comp
          (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
    exact hF.mul h.lintegral_prod_right'
  rw [←lintegral_const_mul _ hout]
  apply lintegral_congr
  intro e
  rw [fiberDensity_lintegral hR]
  ring

def sharpPairSet (R:ℝ) (k:E) : Set (E×E) :=
  {p | rectangleFour k p.1 p.2∈CoareaNormalization.allFourFlags R}

theorem sharpPairSet_measurable (R:ℝ) (k:E) : MeasurableSet (sharpPairSet R k) :=
  (CoareaNormalization.allFourFlags_measurable _).preimage
    (rectangleFour_continuous.measurable.comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))

def fixedEnergyMeasure (R:ℝ) (k:E) : Measure ℝ :=
  Measure.map (fun p:E×E=>CoareaNormalization.energy (rectangleFour k p.1 p.2))
    (((volume:Measure E).prod volume).restrict (sharpPairSet R k))

/-- Equality of actual measures, with a density whose zero-energy
representative was independently shown continuous. -/
theorem fixedEnergyMeasure_eq_withDensity {R:ℝ} (hR:0≤R) (k:E) :
    fixedEnergyMeasure R k=(volume:Measure ℝ).withDensity (fiberDensity R k) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [fixedEnergyMeasure,lintegral_map hF (by
    simp_rw [rectangleFour_energy]
    fun_prop),lintegral_withDensity_eq_lintegral_mul _ (fiberDensity_measurable hR k) hF,
    ←lintegral_indicator (sharpPairSet_measurable R k)]
  have h := sharp_energy_density hR k F hF
  calc
    _ = ∫⁻p:E×E,(CoareaNormalization.allFourFlags R).indicator
        (fun q:FourMomenta=>F (CoareaNormalization.energy q)) (rectangleFour k p.1 p.2)
        ∂((volume:Measure E).prod volume) := by
      apply lintegral_congr
      intro p
      by_cases hp:p∈sharpPairSet R k
      · simp only [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show rectangleFour k p.1 p.2∈CoareaNormalization.allFourFlags R from hp)]
      · simp only [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show rectangleFour k p.1 p.2∉CoareaNormalization.allFourFlags R from hp)]
    _ = _ := by simpa only [mul_comm] using h

end
end Resonance.FixedEnergyDensity
