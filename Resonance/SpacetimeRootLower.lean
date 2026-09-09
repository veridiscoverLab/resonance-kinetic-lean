import Resonance.SpacetimeMultiplierOperators
import Resonance.LpLowerMultiplier

/-! Fixed positive ratio bounds survive on all four legs of the same
joint measure. They remove its whole root multiplier without any uniform
smallness assertion at the cube corners. -/
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace Resonance.SpacetimeRootLower
noncomputable section
open SpacetimePairing SpacetimeRootMultiplier SpacetimeMultiplierOperators
open LpOperators LpFixedTestOperators

theorem root_lower_ae {R : ℝ} (hR : 0 ≤ R) (T : ℝ)
    (θ : Base → Thermodynamics.Parameter) {b : Source → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hb : ∀ᵐ z ∂sourceMeasure R T, m ≤ b z) :
    ∀ᵐ p ∂SpacetimeRJMeasure.measure R T θ, m^2 ≤ |root b p| := by
  have hlegs : ∀ᵐ p ∂SpacetimeRJMeasure.measure R T θ,
      ∀ i : Fin 4, m ≤ b (leg i p) := by
    rw [ae_all_iff]
    intro i
    exact (SpacetimeRJMeasure.leg_quasiMeasurePreserving hR T θ i).ae hb
  filter_upwards [hlegs] with p hp
  have hprod : m^4 ≤ ∏ i : Fin 4, b (leg i p) := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => hm)
        (fun i (_ : i ∈ Finset.univ) => hp i))
  have hs := Real.sqrt_le_sqrt hprod
  have he : m^4 = (m^2)^2 := by ring
  rw [he,Real.sqrt_sq (sq_nonneg m)] at hs
  simpa only [root,abs_of_nonneg (Real.sqrt_nonneg _)] using hs

theorem remove_root_multiplier {R : ℝ} (hR : 0 < R) (T : ℝ)
    (θ : Base → Thermodynamics.Parameter) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {b : ι → Source → ℝ} {m C : ℝ}
    (hm : 0 < m) (hC : 1 ≤ C)
    (hb : ∀ n, AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hl : ∀ n, ∀ᵐ z ∂sourceMeasure R T, m ≤ b n z)
    (hu : ∀ n, ∀ᵐ z ∂sourceMeasure R T, |b n z| ≤ C)
    (hc : TendstoInMeasure (sourceMeasure R T) b l (fun _ => 1))
    {v : ι → Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)}
    {u : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)}
    (hcurrent : Tendsto (fun n => multiplyCLM (root_memLp hR.le T θ (hb n) (hu n))
      (v n)) l (𝓝 u)) : Tendsto v l (𝓝 u) := by
  apply LpLowerMultiplier.remove_moving_multiplier
    (fun n => root_memLp hR.le T θ (hb n) (hu n)) (sq_pos_of_pos hm)
    (fun n => root_lower_ae hR.le T θ hm.le (hl n)) hcurrent
  have hone : ∀ᵐ z ∂sourceMeasure R T, |(1 : ℝ)| ≤ C :=
    ae_of_all _ (fun _ => by simpa using hC)
  have h := root_fixed_test_operator_strong hR.le T θ hb aestronglyMeasurable_const hu hone hc u
  have he := multiply_eq_id (root_memLp hR.le T θ aestronglyMeasurable_const hone)
    (ae_of_all _ (fun _ => by simp [root]))
  simpa only [he,ContinuousLinearMap.one_apply] using h

end
end Resonance.SpacetimeRootLower
