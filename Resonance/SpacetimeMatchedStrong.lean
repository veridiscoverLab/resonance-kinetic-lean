import Resonance.SpacetimeFullRecovery
import Resonance.SpacetimeMultiplierOperators
import Resonance.HilbertOperatorConvergence

/-! Strong recovery of the entire original weighted source, including all
five kernel coordinates. The constraints are the actual analysisMap of the
same multiplied source; no weighted orthogonal-projection replacement occurs. -/
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace Resonance.SpacetimeMatchedStrong
noncomputable section
open Thermodynamics SpacetimePairing SpacetimeReference SpacetimeDifference
open SpacetimeMultiplierOperators SpacetimeFullRecovery LpOperators LpFixedTestOperators
open ProductL2Slices PhysicalFiveBasis

theorem full_source_strong {R m M T : ℝ} (hR : 0 < R) (hm0 : 0 < m) (hM : 1 ≤ M)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K ⊆ positiveDomain R)
    {θ : Base → Parameter} (hm : Measurable θ) (hθ : ∀ᵐ a ∂baseMeasure T, θ a ∈ K)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {b : ι → Source → ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hbnd : ∀ n, ∀ᵐ z ∂sourceMeasure R T, |b n z| ≤ M)
    (hlo : ∀ n, ∀ᵐ z ∂sourceMeasure R T, m ≤ b n z)
    (hc : TendstoInMeasure (sourceMeasure R T) b l (fun _ => 1))
    {y : ι → Space R T} {u : Space R T}
    (hmatch : ∀ n, ∀ᵐ a ∂baseMeasure T, ∀ ha : θ a ∈ positiveDomain R,
      analysisMap hR ha (slice (multiplyCLM (source_memLp hR T (hb n) (hbnd n)) (y n)) a) = 0 ∧
        analysisMap hR ha (slice u a) = 0)
    (hquot : Tendsto (fun n => physicalDifference hR T hK hpos hm hθ (y n)) l
      (𝓝 (physicalDifference hR T hK hpos hm hθ u))) : Tendsto y l (𝓝 u) := by
  obtain ⟨C,hC,hrec⟩ := full_recovery hR hm0 (le_trans zero_le_one hM) hK hpos
  have hone : ∀ᵐ z ∂sourceMeasure R T, |(1 : ℝ)| ≤ M :=
    ae_of_all _ (fun _ => by simpa using hM)
  have hmul := source_fixed_test_strong hR T hb aestronglyMeasurable_const hbnd hone hc u
  have hid := multiply_eq_id (source_memLp hR T aestronglyMeasurable_const hone)
    (ae_of_all _ (fun _ => rfl))
  rw [hid,ContinuousLinearMap.one_apply] at hmul
  have herr : Tendsto (fun n => ‖(multiplyCLM (source_memLp hR T (hb n) (hbnd n))-1) u‖ ^ 2)
      l (𝓝 0) := by
    have h := (hmul.sub (tendsto_const_nhds (x := u))).norm.pow 2
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply] using h
  have hdiff : Tendsto
      (fun n => ‖physicalDifference hR T hK hpos hm hθ (y n-u)‖ ^ 2) l (𝓝 0) := by
    have h := (hquot.sub (tendsto_const_nhds
      (x := physicalDifference hR T hK hpos hm hθ u))).norm.pow 2
    simpa only [map_sub,sub_self,norm_zero,zero_pow (by norm_num : 2≠0)] using h
  have hn : Tendsto (fun n => ‖y n-u‖ ^ 2) l (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) _
      (by simpa only [zero_add,mul_zero] using (hdiff.add herr).const_mul C)
    intro n
    apply hrec T θ hm hθ (b n) (source_memLp hR T (hb n) (hbnd n)) _ (y n) u (hmatch n)
    apply (reference_volume_equivalent hR T).1.ae_le
    filter_upwards [hlo n,hbnd n] with z hz hu
    exact ⟨hz,(le_abs_self _).trans hu⟩
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  have heq : (fun n => Real.sqrt (‖y n-u‖ ^ 2)) = fun n => ‖y n-u‖ :=
    funext (fun n => Real.sqrt_sq (norm_nonneg _))
  change Tendsto (fun n => Real.sqrt (‖y n-u‖ ^ 2)) l (𝓝 (Real.sqrt 0)) at hs
  rw [heq,Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

theorem matched_product_strong {R T M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {b : ι → Source → ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hbnd : ∀ n, ∀ᵐ z ∂sourceMeasure R T, |b n z| ≤ M)
    (hc : TendstoInMeasure (sourceMeasure R T) b l (fun _ => 1))
    {y : ι → Space R T} {u : Space R T} (hy : Tendsto y l (𝓝 u)) :
    Tendsto (fun n => multiplyCLM (source_memLp hR T (hb n) (hbnd n)) (y n)) l (𝓝 u) := by
  let B n := multiplyCLM (source_memLp hR T (hb n) (hbnd n))
  have hnorm : ∀ n, ‖B n‖ ≤ M := fun n => multiply_norm_bound _
    (le_trans zero_le_one hM) ((reference_volume_equivalent hR T).1.ae_le (hbnd n))
  have hone : ∀ᵐ z ∂sourceMeasure R T, |(1 : ℝ)| ≤ M :=
    ae_of_all _ (fun _ => by simpa using hM)
  have hfixed : ∀ v : Space R T, Tendsto (fun n => B n v) l (𝓝 v) := by
    intro v
    have h := source_fixed_test_strong hR T hb aestronglyMeasurable_const hbnd hone hc v
    have hid := multiply_eq_id (source_memLp hR T aestronglyMeasurable_const hone)
      (ae_of_all _ (fun _ => rfl))
    simpa only [hid,ContinuousLinearMap.one_apply] using h
  exact HilbertOperatorConvergence.strong_on_moving B 1 hnorm hfixed hy

end
end Resonance.SpacetimeMatchedStrong
