import Resonance.CollisionFrequencyPositive

/-! Fixed physical output and varying energy shell.  The sharp flags
remain intact, including boundary outputs. -/
open Real Set MeasureTheory Metric
open scoped ENNReal NNReal EuclideanGeometry Topology
namespace Resonance.EnergyFiberContinuity
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea Resonance.PlaneGlobal Resonance.CollisionFiber
open Resonance.FiberContinuity Resonance.CollisionFrequency

theorem fixed_output_shell_measurable (k:E) (e:ℝ) :
    Measurable (fun b:FiberParameters=>planeShell (k,b) e) := by
  exact planeShell_joint_measurable.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem fixed_output_shell_box {R:ℝ} (hR:0≤R) (k:E) (e:ℝ)
    {b:FiberParameters} (hb:planeShell (k,b) e∈CoareaNormalization.allFourFlags R) :
    b∈fiberBox R := by
  have h := (planeShell_flags_bounds hR (k,b) e hb).1
  exact ⟨by simpa [abs_of_nonneg hR] using h.2.1,
    by simpa [abs_of_nonneg hR] using h.2.2⟩

theorem fixed_output_sharp_continuousAt_zero (R:ℝ)
    (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ) (k:E)
    (hk:k∈ResonantMeasure.cube R) (b:FiberParameters)
    (hb:∀i:Fin 4,i≠0→∀j:Fin 3,|fiberFour k b i j|≠R) :
    ContinuousAt (fun e:ℝ=>CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e)) 0 := by
  have hc := planeShell_continuous (k,b)
  have hcoords : ∀ᶠe in 𝓝 (0:ℝ),∀i:Fin 4,i≠0→∀j:Fin 3,
      (|planeShell (k,b) e i j|≤R ↔ |fiberFour k b i j|≤R) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi:i=0
    · exact Filter.Eventually.of_forall (fun _ h=>(h hi).elim)
    · apply Filter.Eventually.mono ?_ (fun _ h _=>h)
      apply Filter.eventually_all.mpr
      intro j
      have hout : Continuous (fun q:FourMomenta=>|q i j|) := by fun_prop
      exact CoareaGlobal.eventually_le_iff_of_continuousAt
        (a:=0) (b:=R) (hout.comp hc).continuousAt (hb i hi j)
  have hflags : ∀ᶠe in 𝓝 (0:ℝ),
      (planeShell (k,b) e∈CoareaNormalization.allFourFlags R ↔
        fiberFour k b∈CoareaNormalization.allFourFlags R) := by
    filter_upwards [hcoords] with e he
    change (∀i,∀j,|planeShell (k,b) e i j|≤R) ↔ (∀i,∀j,|fiberFour k b i j|≤R)
    apply forall_congr'
    intro i
    by_cases hi:i=0
    · subst i
      exact iff_of_true hk hk
    · exact forall_congr' (fun j=>he i hi j)
  by_cases h0:fiberFour k b∈CoareaNormalization.allFourFlags R
  · have heq : (fun e:ℝ=>CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e))
        =ᶠ[𝓝 0] (fun e=>Φ (planeShell (k,b) e)) := by
      filter_upwards [hflags] with e he
      exact Set.indicator_of_mem (he.mpr h0) Φ
    change Filter.Tendsto _ _ (𝓝 (CoareaNormalization.sharpReadout R Φ (fiberFour k b)))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem h0]
    exact (hΦ.comp hc).continuousAt.tendsto.congr' heq.symm
  · have heq : (fun e:ℝ=>CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e))
        =ᶠ[𝓝 0] (fun _=>0) := by
      filter_upwards [hflags] with e he
      exact Set.indicator_of_notMem (fun h=>h0 (he.mp h)) Φ
    change Filter.Tendsto _ _ (𝓝 (CoareaNormalization.sharpReadout R Φ (fiberFour k b)))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem h0]
    exact tendsto_const_nhds.congr' heq.symm

def energyFiberReadout (R:ℝ) (Φ:FourMomenta→ℝ) (k:E) (e:ℝ) : ℝ :=
  (1/2:ℝ)*(∫b,CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e) ∂fiberBase)

theorem fixed_output_sharp_integrable {R B:ℝ} (hR:0≤R) (hB:0≤B)
    (Φ:FourMomenta→ℝ) (hΦ:Measurable Φ)
    (hbound:∀q∈CoareaNormalization.allFourFlags R,‖Φ q‖≤B) (k:E) (e:ℝ) :
    Integrable (fun b:FiberParameters=>CoareaNormalization.sharpReadout R Φ
      (planeShell (k,b) e)) fiberBase := by
  let f : FiberParameters→ℝ := fun b=>CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e)
  have hm : Measurable f :=
    (CoareaNormalization.sharpReadout_measurable R hΦ).comp (fixed_output_shell_measurable k e)
  have hbnd (b:FiberParameters) : ‖f b‖≤B := by
    by_cases hb:planeShell (k,b) e∈CoareaNormalization.allFourFlags R
    · simp only [f,CoareaNormalization.sharpReadout,Set.indicator_of_mem hb]
      exact hbound _ hb
    · simp only [f,CoareaNormalization.sharpReadout,Set.indicator_of_notMem hb,norm_zero]
      exact hB
  have hi : Integrable f (finiteFiberBase R) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (ae_of_all _ hbnd)
  have hj : Integrable ((fiberBox R).indicator f) fiberBase :=
    (integrable_indicator_iff (fiberBox_measurable R)).mpr hi
  apply hj.congr
  apply ae_of_all
  intro b
  by_cases hb:b∈fiberBox R
  · exact Set.indicator_of_mem hb f
  · rw [Set.indicator_of_notMem hb]
    symm
    exact Set.indicator_of_notMem (fun h=>hb (fixed_output_shell_box hR k e h)) Φ

theorem energyFiberReadout_zero (R:ℝ) (Φ:FourMomenta→ℝ) (hΦ:Measurable Φ) (k:E) :
    energyFiberReadout R Φ k 0=fiberReadout R Φ k :=
  (fiberReadout_base R Φ hΦ k).symm

theorem energyFiberReadout_box {R:ℝ} (hR:0≤R) (Φ:FourMomenta→ℝ) (k:E) (e:ℝ) :
    energyFiberReadout R Φ k e=(1/2:ℝ)*
      ∫b,CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e) ∂finiteFiberBase R := by
  unfold energyFiberReadout
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro b hb
  exact Set.indicator_of_notMem (fun h=>hb (fixed_output_shell_box hR k e h)) Φ

/-- Continuity at the zero energy level holds for every fixed output
in the closed cube, not merely for almost every physical output. -/
theorem energyFiberReadout_continuousAt_zero {R:ℝ} (hR:0≤R)
    (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ) (k:E)
    (hk:k∈ResonantMeasure.cube R) : ContinuousAt (energyFiberReadout R Φ k) 0 := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  have heq : energyFiberReadout R Φ k=fun e=>(1/2:ℝ)*
      ∫b,CoareaNormalization.sharpReadout R Φ (planeShell (k,b) e) ∂finiteFiberBase R :=
    funext (energyFiberReadout_box hR Φ k)
  rw [heq]
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_integral_filter_of_dominated_convergence (fun _:FiberParameters=>B)
  · exact Filter.Eventually.of_forall (fun e=>
      ((CoareaNormalization.sharpReadout_measurable R hΦ.measurable).comp
        (fixed_output_shell_measurable k e)).aestronglyMeasurable)
  · apply Filter.Eventually.of_forall
    intro e
    apply ae_of_all
    intro b
    by_cases hb:planeShell (k,b) e∈CoareaNormalization.allFourFlags R
    · rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem hb]
      exact hbound _ hb
    · rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem hb,norm_zero]
      exact hB
  · exact integrable_const B
  · have ha := ae_restrict_of_ae (s:=fiberBox R) (fiber_nonoutput_faces_avoided k R)
    filter_upwards [ha] with b hb
    exact (fixed_output_sharp_continuousAt_zero R Φ hΦ k hk b hb).tendsto

def energyFiberMass (R:ℝ) (k:E) : ℝ→ℝ := energyFiberReadout R (fun _=>1) k

theorem energyFiberMass_zero (R:ℝ) (k:E) :
    energyFiberMass R k 0=geometricFrequency R k :=
  energyFiberReadout_zero R (fun _=>1) measurable_const k

theorem energyFiberMass_continuousAt_zero {R:ℝ} (hR:0≤R) (k:E)
    (hk:k∈ResonantMeasure.cube R) : ContinuousAt (energyFiberMass R k) 0 :=
  energyFiberReadout_continuousAt_zero hR (fun _=>1) continuous_const k hk

end
end Resonance.EnergyFiberContinuity
