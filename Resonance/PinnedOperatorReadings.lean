import Resonance.PinnedRNReadings
import Resonance.PinnedOperator
import Resonance.PinnedSmoothTestUniqueness

/-! Exact original form and operator readings. The C² source is only
assumed in the operator domain when an operator output is asserted;
no smooth form-core or automatic C² operator-domain assertion is used. -/
open Set MeasureTheory Filter
open scoped ContDiff ComplexConjugate
namespace Resonance.PinnedOperatorReadings
noncomputable section
open PinnedPeriodicity PinnedClassificationFinal PinnedLegACCircle
open PinnedMaximalDifference PinnedSmoothDomain PinnedClosedForm PinnedOperator
open PinnedTorusPermutations PinnedWeightedReadings
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem paperInner_reading (z : Source) (ψ : C(PinnedPeriodicity.Circle,ℂ)) :
    paperInner z (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ ψ)=
      ∫x,star (ψ x)*z x∂circleHaar := by
  rw [paperInner,L2.inner_def]
  have hψa : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ ψ :
      PinnedPeriodicity.Circle→ℂ)=ᵐ[circleHaar] ψ := ContinuousMap.coeFn_toLp circleHaar ψ
  apply integral_congr_ae
  filter_upwards [hψa] with x hx
  simp only [hx,RCLike.inner_apply]
  change z x*star (ψ x)=star (ψ x)*z x
  ring

theorem paperForm_reading {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (ha0 : ∀q,0≤a q) (hasym : SymmetricWeight a)
    (φ ψ : C(PinnedPeriodicity.Circle,ℂ))
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ2 : ContDiff ℝ 2 (periodicLift ψ)) (γ : ℝ) :
    paperForm hd0 hdU a γ
      ⟨ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ,continuous_C2_mem_domain hd0 hdU ha φ hφ2⟩
      ⟨ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ ψ,continuous_C2_mem_domain hd0 hdU ha ψ hψ2⟩=
      (γ:ℂ)*(∫k,difference φ k*star (ψ (circleLeg 0 k))∂weightedCoarea d a) := by
  rw [paperForm_integral]
  have heφ : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ :
      PinnedPeriodicity.Circle→ℂ)=ᵐ[circleHaar] φ := ContinuousMap.coeFn_toLp circleHaar φ
  have heψ : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ ψ :
      PinnedPeriodicity.Circle→ℂ)=ᵐ[circleHaar] ψ := ContinuousMap.coeFn_toLp circleHaar ψ
  have hφa := difference_ae_congr hd0 hdU a heφ
  have hψa := difference_ae_congr hd0 hdU a heψ
  calc
    _ = (γ/4:ℂ)*(∫k,difference φ k*star (difference ψ k)∂weightedCoarea d a) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hφa,hψa] with k hk hl
      simp only [hk,hl]
      rfl
    _ = _ := weighted_quarter_identity hd0 hdU ha ha0 hasym φ.continuous hφ2 ψ.continuous γ

theorem operator_tested_reading {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (ha0 : ∀q,0≤a q) (hasym : SymmetricWeight a)
    {γ : ℝ} (hγ : 0≤γ) (φ ψ : C(PinnedPeriodicity.Circle,ℂ))
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ2 : ContDiff ℝ 2 (periodicLift ψ))
    (z : Source) (hz : (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ,z)∈
      (associatedOperator hd0 hdU a γ).graph) :
    (∫x,star (ψ x)*z x∂circleHaar)=
      (γ:ℂ)*(∫k,difference φ k*star (ψ (circleLeg 0 k))∂weightedCoarea d a) := by
  obtain ⟨hx,hv⟩ := (associatedOperator_paper_graph_iff hd0 hdU ha hγ _ _).mp hz
  have he := hv ⟨ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ ψ,
    continuous_C2_mem_domain hd0 hdU ha ψ hψ2⟩
  rw [paperInner_reading] at he
  exact he.trans (paperForm_reading hd0 hdU ha ha0 hasym φ ψ hφ2 hψ2 γ)

end
end Resonance.PinnedOperatorReadings
