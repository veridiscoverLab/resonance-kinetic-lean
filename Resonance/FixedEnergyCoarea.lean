import Resonance.EnergyFiberContinuity

/-! Actual fixed-output energy disintegration before imposing the
sharp flags.  Both maps and their Jacobians are proved. -/
open Real Set MeasureTheory Metric
open scoped ENNReal NNReal EuclideanGeometry Topology
namespace Resonance.FixedEnergyCoarea
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea Resonance.PlaneGlobal Resonance.CollisionFiber

def normalFiberBase : Measure FiberParameters := rayMeasure.prod (volume:Measure E2)
instance normalFiberBase_sigmaFinite : SigmaFinite normalFiberBase := by
  unfold normalFiberBase
  infer_instance

theorem normalFiberBase_from_fiberBase : normalFiberBase=fiberBase.withDensity
    (fun b:FiberParameters=>ENNReal.ofReal (b.1.2:ℝ)) := by
  rw [normalFiberBase,rayMeasure_from_rayOne,prod_withDensity_left (by fun_prop)]
  rfl

theorem twice_normalFiberBase : fiberBase.withDensity
    (fun b:FiberParameters=>ENNReal.ofReal (2*(b.1.2:ℝ)))=(2:ℝ≥0∞)•normalFiberBase := by
  rw [normalFiberBase_from_fiberBase,←withDensity_smul _ (by fun_prop)]
  congr 1
  funext b
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  norm_num

def energyScale (q:FiberParameters×ℝ) : FiberParameters×ℝ :=
  (q.1,q.2/(2*(q.1.1.2:ℝ)))

theorem energyScale_measurable : Measurable energyScale := by unfold energyScale; fun_prop

theorem energyScale_map : Measure.map energyScale (fiberBase.prod (volume:Measure ℝ))=
    (fiberBase.withDensity (fun b=>ENNReal.ofReal (2*(b.1.2:ℝ)))).prod volume := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply energyScale_measurable hs,
    Measure.prod_apply (hs.preimage energyScale_measurable),Measure.prod_apply hs,
    lintegral_withDensity_eq_lintegral_mul fiberBase (by fun_prop)
      (measurable_measure_prodMk_left hs)]
  apply lintegral_congr
  intro b
  have hsection : MeasurableSet ((Prod.mk b)⁻¹'s) := hs.preimage measurable_prodMk_left
  have hm := Measure.map_apply (μ:=(volume:Measure ℝ))
    (by fun_prop : Measurable (fun e:ℝ=>e/(2*(b.1.2:ℝ)))) hsection
  rw [normal_scale_volume b.1.2.property,Measure.smul_apply] at hm
  simpa only [energyScale,Set.preimage_preimage,Pi.mul_apply,smul_eq_mul] using hm.symm

def energyBase : Measure (FiberParameters×ℝ) := (1/2:ℝ≥0∞)•fiberBase.prod volume

theorem energyScale_preserving : MeasurePreserving energyScale energyBase
    (normalFiberBase.prod (volume:Measure ℝ)) := by
  refine ⟨energyScale_measurable,?_⟩
  rw [energyBase,Measure.map_smul,energyScale_map,twice_normalFiberBase,
    Measure.prod_smul_left,smul_smul]
  norm_num only [one_div]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_smul]

def normalFiberShuffle : (FiberParameters×ℝ) ≃ᵐ (Ray×(ℝ×E2)) :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ray) MeasurableEquiv.prodComm)

theorem normalFiberShuffle_preserving : MeasurePreserving normalFiberShuffle
    (normalFiberBase.prod (volume:Measure ℝ))
    (rayMeasure.prod ((volume:Measure ℝ).prod (volume:Measure E2))) := by
  exact (measurePreserving_prodAssoc rayMeasure (volume:Measure E2) (volume:Measure ℝ)).trans
    ((MeasurePreserving.id rayMeasure).prod Measure.measurePreserving_swap)

def energyToPair (q:FiberParameters×ℝ) : E×E :=
  rayNormal (normalFiberShuffle (energyScale q))

theorem energyToPair_preserving : MeasurePreserving energyToPair energyBase
    ((volume:Measure E).prod volume) :=
  rayNormal_preserving.comp (normalFiberShuffle_preserving.comp energyScale_preserving)

theorem energyToPair_quartet (k:E) (b:FiberParameters) (e:ℝ) :
    rectangleFour k (energyToPair (b,e)).1 (energyToPair (b,e)).2=planeShell (k,b) e := rfl

/-- Full fixed-k coarea identity for every nonnegative measurable
quartet test.  Inserting the original four flags preserves the identity. -/
theorem fixed_output_energy_lintegral (k:E) (F:FourMomenta→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻p:E×E,F (rectangleFour k p.1 p.2) ∂((volume:Measure E).prod volume))=
      (1/2:ℝ≥0∞)*(∫⁻e:ℝ,∫⁻b:FiberParameters,F (planeShell (k,b) e) ∂fiberBase) := by
  have hrect : Measurable (fun p:E×E=>F (rectangleFour k p.1 p.2)) :=
    hF.comp (rectangleFour_continuous.measurable.comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  have he := lintegral_map (μ:=energyBase) hrect energyToPair_preserving.measurable
  rw [energyToPair_preserving.map_eq] at he
  rw [he]
  change (∫⁻q:FiberParameters×ℝ,F (planeShell (k,q.1) q.2) ∂energyBase)=_
  rw [energyBase,lintegral_smul_measure,smul_eq_mul]
  have hm : Measurable (fun q:FiberParameters×ℝ=>F (planeShell (k,q.1) q.2)) :=
    hF.comp (planeShell_joint_measurable.comp
      (measurable_snd.prodMk (measurable_const.prodMk measurable_fst)))
  rw [lintegral_prod _ hm.aemeasurable,lintegral_lintegral_swap hm.aemeasurable]

end
end Resonance.FixedEnergyCoarea
