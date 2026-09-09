import Resonance.SpacetimeCurrentConvergence

/-! The complete signed adjoint return, with both moving multipliers kept.
This is a Riesz representative in the original reference-frequency metric.
Identification with the physical nonlinear collision output additionally uses
its actual weak equation and the density normalization of that metric. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology
namespace Resonance.SpacetimeCurrentReturn
noncomputable section
open SpacetimePairing SpacetimeReference SpacetimeRootMultiplier
open SpacetimeMultiplierOperators LpOperators LpFixedTestOperators
variable {R : ℝ} (hR : 0<R) (T : ℝ) {K : Set Thermodynamics.Parameter}
  (hK : IsCompact K) (hpos : K⊆Thermodynamics.positiveDomain R)
  {θ : Base→Thermodynamics.Parameter} (hm : Measurable θ)
  (hθ : ∀ᵐz∂baseMeasure T,θ z∈K)
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
  {b d : ι→Source→ℝ} {C : ℝ} (hC : 1≤C)
  (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
  (hd : ∀n,AEStronglyMeasurable (d n) (sourceMeasure R T))
  (hbnd : ∀n,∀ᵐz∂sourceMeasure R T,|b n z|≤C)
  (hdnd : ∀n,∀ᵐz∂sourceMeasure R T,|d n z|≤C)

def signedReturn (n : ι) (J : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)) : Space R T :=
  -(multiplyCLM (source_memLp hR T (hd n) (hdnd n))
    ((SpacetimeDifference.physicalDifference hR T hK hpos hm hθ).adjoint
      (multiplyCLM (root_memLp hR.le T θ (hb n) (hbnd n)) J)))

include hC in
theorem signedReturn_strong
    (hbconv : TendstoInMeasure (sourceMeasure R T) b l (fun _=>1))
    (hdconv : TendstoInMeasure (sourceMeasure R T) d l (fun _=>1))
    {J : ι→Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)}
    {J0 : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)} (hJ : Tendsto J l (𝓝 J0)) :
    Tendsto (fun n=>signedReturn hR T hK hpos hm hθ hb hd hbnd hdnd n (J n)) l
      (𝓝 (-(SpacetimeDifference.physicalDifference hR T hK hpos hm hθ).adjoint J0)) := by
  let RR:=SpacetimeDifference.physicalDifference hR T hK hpos hm hθ
  let A n:=multiplyCLM (root_memLp hR.le T θ (hb n) (hbnd n))
  let B n:=multiplyCLM (source_memLp hR T (hd n) (hdnd n))
  have hone : ∀ᵐz∂sourceMeasure R T,|(1:ℝ)|≤C:=ae_of_all _ (fun _=>by simpa using hC)
  have hAf : ∀V,Tendsto (fun n=>A n V) l (𝓝 ((1: _→L[ℝ]_) V)) := by
    intro V
    have hh:=root_fixed_test_operator_strong hR.le T θ hb aestronglyMeasurable_const
      hbnd hone hbconv V
    have he:=multiply_eq_id (root_memLp hR.le T θ aestronglyMeasurable_const hone)
      (ae_of_all _ (fun _=>by simp [root]))
    simpa only [he] using hh
  have hBf : ∀v,Tendsto (fun n=>B n v) l (𝓝 ((1: _→L[ℝ]_) v)) := by
    intro v
    have hh:=source_fixed_test_strong hR T hd aestronglyMeasurable_const hdnd hone hdconv v
    have he:=multiply_eq_id (source_memLp hR T aestronglyMeasurable_const hone)
      (ae_of_all _ (fun _=>rfl))
    simpa only [he] using hh
  have hAn : ∀n,‖A n‖≤C^2 := by
    intro n
    exact multiply_norm_bound _ (sq_nonneg C)
      ((SpacetimeRJMeasure.measure_absolutelyContinuous R T θ).ae_le (root_bound hR.le T (hbnd n)))
  have hBn : ∀n,‖B n‖≤C := by
    intro n
    exact multiply_norm_bound _ (by linarith)
      ((reference_volume_equivalent hR T).1.ae_le (hdnd n))
  have ha:=HilbertOperatorConvergence.strong_on_moving A 1 hAn hAf hJ
  have hr:=RR.adjoint.continuous.tendsto _ |>.comp ha
  have hout:=HilbertOperatorConvergence.strong_on_moving B 1 hBn hBf hr
  simpa only [ContinuousLinearMap.one_apply] using hout.neg

end
end Resonance.SpacetimeCurrentReturn
