import Resonance.PinnedOperatorWeakIdentification

/-! All four output positions of the same signed current. The two
incoming outputs agree and both outgoing outputs have the opposite sign.
No source term or test is reselected after taking a limit. -/
open Set MeasureTheory Filter
open scoped ContDiff
namespace Resonance.PinnedAllLegOutputs
noncomputable section
open PinnedPeriodicity PinnedClassificationFinal PinnedLegACCircle
open PinnedMaximalDifference PinnedSmoothDomain PinnedOperator
open PinnedTorusPermutations PinnedQuarterSymmetrization PinnedWeightedReadings
open PinnedRNReadings PinnedOperatorWeakIdentification
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

def outputSign (i : Fin 4) : ℝ := if i.val<2 then 1 else -1

theorem legCurrent_sign {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (hasym : SymmetricWeight a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) (i : Fin 4) :
    legCurrent d a φ ψ i=(outputSign i:ℂ)*legCurrent d a φ ψ 0 := by
  have hI := legCurrent_transform hd0 hdU ha hasym hφ hφ2 hψ 0 0
  have hP := legCurrent_transform hd0 hdU ha hasym hφ hφ2 hψ 2 0
  have hO := legCurrent_transform hd0 hdU ha hasym hφ hφ2 hψ 1 2
  change legCurrent d a φ ψ 0=(1:ℂ)*legCurrent d a φ ψ 1 at hI
  change legCurrent d a φ ψ 0=((-1:ℝ):ℂ)*legCurrent d a φ ψ 2 at hP
  change legCurrent d a φ ψ 2=(1:ℂ)*legCurrent d a φ ψ 3 at hO
  simp only [one_mul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] at hI hP hO
  fin_cases i <;> norm_num [outputSign]
  · exact hI.symm
  · change legCurrent d a φ ψ 2 = -legCurrent d a φ ψ 0
    linear_combination hP
  · change legCurrent d a φ ψ 3 = -legCurrent d a φ ψ 0
    rw [←hO]
    linear_combination hP

theorem weighted_leg_sign {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (ha0 : ∀q,0≤a q) (hasym : SymmetricWeight a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) (i : Fin 4) :
    (∫k,difference φ k*star (ψ (circleLeg i k))∂weightedCoarea d a)=
      (outputSign i:ℂ)*(∫k,difference φ k*star (ψ (circleLeg 0 k))∂weightedCoarea d a) := by
  rw [weighted_integral ha ha0,weighted_integral ha ha0]
  simpa only [legCurrent,legSource,mul_assoc,mul_left_comm,mul_comm] using
    legCurrent_sign hd0 hdU ha hasym hφ hφ2 hψ i

theorem all_leg_RN_outputs {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (ha0 : ∀q,0≤a q) (hasym : SymmetricWeight a)
    {γ : ℝ} (hγ : 0≤γ) (φ : C(PinnedPeriodicity.Circle,ℂ))
    (hφ2 : ContDiff ℝ 2 (periodicLift φ))
    (z : Source) (hz : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ,z)∈
      (associatedOperator hd0 hdU a γ).graph) (i : Fin 4) :
    ∃g:PinnedPeriodicity.Circle→ℂ,Integrable g circleHaar ∧
      g=ᵐ[circleHaar] (fun x=>(outputSign i:ℂ)*z x) ∧
      (∀s,MeasurableSet s→(∫x in s,g x∂circleHaar)=
        ∫k in (circleLeg i)⁻¹' s,(γ:ℂ)*difference φ k∂weightedCoarea d a) ∧
      ∀ψ:C(PinnedPeriodicity.Circle,ℂ),(∫x,star (ψ x)*g x∂circleHaar)=
        (γ:ℂ)*(∫k,difference φ k*star (ψ (circleLeg i k))∂weightedCoarea d a) := by
  obtain ⟨g,hg,he,ht⟩ := exists_all_tested_output hd0 hdU ha φ.continuous hφ2 γ i
  refine ⟨g,hg,?_,he,ht⟩
  have hsz : Integrable (fun x=>(outputSign i:ℂ)*z x) circleHaar :=
    (source_integrable z).const_mul _
  have hzero := PinnedSmoothTestUniqueness.ae_zero_of_smooth_tests (hg.sub hsz) (by
    intro ψ hψ
    let χ : C(PinnedPeriodicity.Circle,ℂ) := star ψ
    have hχ : ContDiff ℝ 2 (periodicLift χ) :=
      (contDiff_infty.mp (Complex.conjCLE.contDiff.comp hψ)) 2
    have hgtest := ht χ
    rw [weighted_leg_sign hd0 hdU ha ha0 hasym φ.continuous hφ2 χ.continuous i] at hgtest
    have hztest := PinnedOperatorReadings.operator_tested_reading hd0 hdU ha ha0 hasym
      hγ φ χ hφ2 hχ z hz
    simp only [χ,ContinuousMap.star_apply,star_star] at hgtest hztest
    have heq : (∫x,ψ x*g x∂circleHaar)=
        (outputSign i:ℂ)*(∫x,ψ x*z x∂circleHaar) := by
      rw [hgtest,hztest]
      ring
    have hiS : (∫x,ψ x*((outputSign i:ℂ)*z x)∂circleHaar)=
        (outputSign i:ℂ)*(∫x,ψ x*z x∂circleHaar) := by
      calc
        _ = ∫x,(outputSign i:ℂ)*(ψ x*z x)∂circleHaar :=
          integral_congr_ae (Eventually.of_forall (fun _=>by ring))
        _ = _ := integral_const_mul _ _
    calc
      _ = ∫x,ψ x*g x-ψ x*((outputSign i:ℂ)*z x)∂circleHaar :=
        integral_congr_ae (Eventually.of_forall (fun _=>mul_sub _ _ _))
      _ = (∫x,ψ x*g x∂circleHaar)-(∫x,ψ x*((outputSign i:ℂ)*z x)∂circleHaar) :=
        integral_sub (ContinuousDensityFunctional.test_integrable circleHaar hg ψ)
          (ContinuousDensityFunctional.test_integrable circleHaar hsz ψ)
      _ = 0 := sub_eq_zero.mpr (heq.trans hiS.symm))
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

end
end Resonance.PinnedAllLegOutputs
