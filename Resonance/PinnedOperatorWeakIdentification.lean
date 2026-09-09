import Resonance.PinnedOperatorReadings

/-! Identification of the genuine Radon--Nikodym weak output with the
original associated operator. The same L¹ density represents all tests
and all measurable sets; equality is actual Haar almost everywhere. -/
open Set MeasureTheory Filter
open scoped ContDiff
namespace Resonance.PinnedOperatorWeakIdentification
noncomputable section
open PinnedPeriodicity PinnedClassificationFinal PinnedLegACCircle
open PinnedMaximalDifference PinnedSmoothDomain PinnedOperator
open PinnedTorusPermutations PinnedRNReadings PinnedOperatorReadings
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem source_integrable (z : Source) : Integrable (z:PinnedPeriodicity.Circle→ℂ) circleHaar :=
  MemLp.integrable (by norm_num : (1:ENNReal)≤2) (Lp.memLp z)

theorem RN_output_eq_operator {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (ha0 : ∀q,0≤a q) (hasym : SymmetricWeight a)
    {γ : ℝ} (hγ : 0≤γ) (φ : C(PinnedPeriodicity.Circle,ℂ))
    (hφ2 : ContDiff ℝ 2 (periodicLift φ))
    (z : Source) (hz : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ,z)∈
      (associatedOperator hd0 hdU a γ).graph)
    {g : PinnedPeriodicity.Circle→ℂ} (hg : Integrable g circleHaar)
    (he : ∀s,MeasurableSet s→(∫x in s,g x∂circleHaar)=
      ∫k in (circleLeg 0)⁻¹' s,(γ:ℂ)*difference φ k∂weightedCoarea d a) :
    g=ᵐ[circleHaar] (z:PinnedPeriodicity.Circle→ℂ) := by
  have hzg := source_integrable z
  have hf : Integrable (fun x=>g x-z x) circleHaar := hg.sub hzg
  have hzero := PinnedSmoothTestUniqueness.ae_zero_of_smooth_tests hf (by
    intro ψ hψ
    let χ : C(PinnedPeriodicity.Circle,ℂ) := star ψ
    have hχ : ContDiff ℝ 2 (periodicLift χ) := by
      exact (contDiff_infty.mp (Complex.conjCLE.contDiff.comp hψ)) 2
    have hgtest := tested_output hd0 hdU ha φ.continuous hφ2 γ 0 hg he χ
    have hztest := operator_tested_reading hd0 hdU ha ha0 hasym hγ φ χ hφ2 hχ z hz
    have heq : (∫x,ψ x*g x∂circleHaar)=(∫x,ψ x*z x∂circleHaar) := by
      simpa only [χ,ContinuousMap.star_apply,star_star] using hgtest.trans hztest.symm
    calc
      _ = ∫x,ψ x*g x-ψ x*z x∂circleHaar := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _=>mul_sub _ _ _)
      _ = (∫x,ψ x*g x∂circleHaar)-(∫x,ψ x*z x∂circleHaar) :=
        integral_sub (ContinuousDensityFunctional.test_integrable circleHaar hg ψ)
          (ContinuousDensityFunctional.test_integrable circleHaar hzg ψ)
      _ = 0 := sub_eq_zero.mpr heq)
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

/-- Original weak-output statement on C² intersected with the literal
operator domain. The RN function exists before all test quantifiers. -/
theorem original_operator_RN_output {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (ha0 : ∀q,0≤a q) (hasym : SymmetricWeight a)
    {γ : ℝ} (hγ : 0≤γ) (φ : C(PinnedPeriodicity.Circle,ℂ))
    (hφ2 : ContDiff ℝ 2 (periodicLift φ))
    (z : Source) (hz : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ,z)∈
      (associatedOperator hd0 hdU a γ).graph) :
    ∃g:PinnedPeriodicity.Circle→ℂ,Integrable g circleHaar ∧
      g=ᵐ[circleHaar] (z:PinnedPeriodicity.Circle→ℂ) ∧
      (∀s,MeasurableSet s→(∫x in s,g x∂circleHaar)=
        ∫k in (circleLeg 0)⁻¹' s,(γ:ℂ)*difference φ k∂weightedCoarea d a) ∧
      ∀ψ:C(PinnedPeriodicity.Circle,ℂ),(∫x,star (ψ x)*g x∂circleHaar)=
        (γ:ℂ)*(∫k,difference φ k*star (ψ (circleLeg 0 k))∂weightedCoarea d a) := by
  obtain ⟨g,hg,he,ht⟩ := exists_all_tested_output hd0 hdU ha φ.continuous hφ2 γ 0
  exact ⟨g,hg,RN_output_eq_operator hd0 hdU ha ha0 hasym hγ φ hφ2 z hz hg he,he,ht⟩

end
end Resonance.PinnedOperatorWeakIdentification
