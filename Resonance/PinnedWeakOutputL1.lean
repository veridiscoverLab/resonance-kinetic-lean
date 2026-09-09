import Resonance.PinnedWeakIntegrability
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-! The actual full-difference collision current has an L¹ output under
each original circle leg. Absolute continuity is supplied by the full pinned
regular coarea, not assumed for an auxiliary graph. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff ComplexConjugate
namespace Resonance.PinnedWeakOutputL1
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedClassificationFinal Resonance.PinnedLegACCircle
open Resonance.PinnedMeasureNormalization Resonance.PinnedMaximalDifference
open Resonance.PinnedSmoothDomain Resonance.PinnedWeakIntegrability
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem real_pushforward_density {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν]
    {T : α→β} (hT : Measurable T) (hAC : μ.map T ≪ ν)
    {f : α→ℝ} (hf : Integrable f μ) :
    ∃g : β→ℝ, Integrable g ν ∧ ∀s, MeasurableSet s →
      (∫x in s,g x ∂ν)=∫x in T⁻¹' s,f x ∂μ := by
  let S : SignedMeasure β := (μ.withDensityᵥ f).map T
  have hS : S ≪ᵥ ν.toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro s hs hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hz
    have hzero : μ (T⁻¹' s)=0 := by
      have h := hAC hz
      rwa [Measure.map_apply hT hs] at h
    change (μ.withDensityᵥ f).map T s=0
    rw [VectorMeasure.map_apply _ hT hs,withDensityᵥ_apply hf (hT hs)]
    simp [Measure.restrict_eq_zero.mpr hzero]
  refine ⟨S.rnDeriv ν,SignedMeasure.integrable_rnDeriv _ _,?_⟩
  intro s hs
  have he := congrArg (fun M : SignedMeasure β=>M s)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq S ν hS)
  change (ν.withDensityᵥ (S.rnDeriv ν)) s=S s at he
  rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at he
  change _=(μ.withDensityᵥ f).map T s at he
  rw [VectorMeasure.map_apply _ hT hs,withDensityᵥ_apply hf (hT hs)] at he
  exact he

theorem complex_pushforward_density {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν]
    {T : α→β} (hT : Measurable T) (hAC : μ.map T ≪ ν)
    {f : α→ℂ} (hf : Integrable f μ) :
    ∃g : β→ℂ, Integrable g ν ∧ ∀s, MeasurableSet s →
      (∫x in s,g x ∂ν)=∫x in T⁻¹' s,f x ∂μ := by
  have hfR : Integrable (fun x=>(f x).re) μ := Complex.reCLM.integrable_comp hf
  have hfI : Integrable (fun x=>(f x).im) μ := Complex.imCLM.integrable_comp hf
  obtain ⟨gR,hR,eR⟩ := real_pushforward_density μ ν hT hAC hfR
  obtain ⟨gI,hI,eI⟩ := real_pushforward_density μ ν hT hAC hfI
  let g : β→ℂ := fun x=>⟨gR x,gI x⟩
  have hg : Integrable g ν := by
    rw [←memLp_one_iff_integrable,←memLp_re_im_iff]
    exact ⟨memLp_one_iff_integrable.mpr hR,memLp_one_iff_integrable.mpr hI⟩
  refine ⟨g,hg,?_⟩
  intro s hs
  apply Complex.ext
  · have hrg := Complex.reCLM.integral_comp_comm (μ:=ν.restrict s) hg.integrableOn
    have hrf := Complex.reCLM.integral_comp_comm (μ:=μ.restrict (T⁻¹' s)) hf.integrableOn
    exact hrg.symm.trans ((eR s hs).trans hrf)
  · have hig := Complex.imCLM.integral_comp_comm (μ:=ν.restrict s) hg.integrableOn
    have hif := Complex.imCLM.integral_comp_comm (μ:=μ.restrict (T⁻¹' s)) hf.integrableOn
    exact hig.symm.trans ((eI s hs).trans hif)

theorem weighted_leg_absolutelyContinuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (i : Fin 4) :
    (weightedCoarea d a).map (circleLeg i) ≪ circleHaar :=
  ((withDensity_absolutelyContinuous _ _).map (circleLeg_continuous i).measurable).trans
    (full_coarea_all_legs_absolutelyContinuous hd0 hdU i)

/-- Actual L¹ weak output, for every fixed periodic C² test and every leg.
The density represents the complete γ a Δφ current on all measurable sets. -/
theorem exists_L1_weak_output {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (γ : ℝ) (i : Fin 4) :
    ∃g : PinnedPeriodicity.Circle→ℂ, Integrable g circleHaar ∧
      ∀s, MeasurableSet s → (∫x in s,g x ∂circleHaar)=
        ∫k in (circleLeg i)⁻¹' s,(γ:ℂ)*difference φ k ∂weightedCoarea d a := by
  have hi : Integrable (difference φ) (weightedCoarea d a) :=
    (integrable_norm_iff (difference_continuous hφ).aestronglyMeasurable).mp
        (difference_norm_integrable_weighted hd0 hdU ha hφ hφ2)
  exact complex_pushforward_density (weightedCoarea d a) circleHaar
    (circleLeg_continuous i).measurable (weighted_leg_absolutelyContinuous hd0 hdU a i)
    (hi.const_mul (γ:ℂ))

end
end Resonance.PinnedWeakOutputL1
