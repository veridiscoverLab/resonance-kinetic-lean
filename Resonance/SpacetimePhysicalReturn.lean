import Resonance.SpacetimePhysicalTests

/-! The full signed return is an element of original physical L²(dt dX dk).
Its pairing is the complete half-difference on the same joint measure; the
actual nonlinear output is identified by its original weak row, separately.
No frequency-weighted Riesz vector is silently called physical collision. -/
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace Resonance.SpacetimePhysicalReturn
noncomputable section
open SpacetimePairing SpacetimeRootMultiplier SpacetimeMultiplierOperators
open SpacetimePhysicalTests LpOperators LpFixedTestOperators
variable {R : ℝ} (hR : 0 < R) (T : ℝ) {K : Set Thermodynamics.Parameter}
  (hK : IsCompact K) (hpos : K ⊆ Thermodynamics.positiveDomain R)
  {θ : Base → Thermodynamics.Parameter} (hm : Measurable θ)
  (hθ : ∀ᵐ a ∂baseMeasure T, θ a ∈ K)

def physicalReturn (J : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)) : PhysicalSpace R T :=
  -(physicalDifference hR T hK hpos hm hθ).adjoint J

include hR hK hpos hm hθ in
theorem complete_pairing_integrable (J : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ))
    (v : PhysicalSpace R T) :
    Integrable (fun p => J p * SpacetimeDifference.rawDifference (v : Source → ℝ) p)
      (SpacetimeRJMeasure.measure R T θ) := by
  have hi := (Lp.memLp J).integrable_mul
    (Lp.memLp (physicalDifference hR T hK hpos hm hθ v))
  apply hi.congr
  filter_upwards [physicalDifference_ae hR T hK hpos hm hθ v] with p hp
  exact congrArg (fun x : ℝ => J p * x) hp

theorem complete_physical_pairing (J : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ))
    (v : PhysicalSpace R T) :
    inner ℝ v (physicalReturn hR T hK hpos hm hθ J) =
      -(∫ p, J p * SpacetimeDifference.rawDifference (v : Source → ℝ) p
        ∂SpacetimeRJMeasure.measure R T θ) := by
  rw [physicalReturn,inner_neg_right,ContinuousLinearMap.adjoint_inner_right,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [physicalDifference_ae hR T hK hpos hm hθ v] with p hp
  change J p * physicalDifference hR T hK hpos hm hθ v p = _
  rw [hp]

theorem reference_metric_dictionary (J : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)) :
    physicalReturn hR T hK hpos hm hθ J =
      (physicalTest hR T hK hpos hm hθ).adjoint
        (-(SpacetimeDifference.physicalDifference hR T hK hpos hm hθ).adjoint J) := by
  rw [physicalReturn,SpacetimePhysicalTests.physicalDifference,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,map_neg]

theorem physical_return_strong {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {b : ι → Source → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (hb : ∀ n, AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hbnd : ∀ n, ∀ᵐ z ∂sourceMeasure R T, |b n z| ≤ C)
    (hc : TendstoInMeasure (sourceMeasure R T) b l (fun _ => 1))
    {J : ι → Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)}
    {J0 : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)} (hJ : Tendsto J l (𝓝 J0)) :
    Tendsto (fun n => physicalReturn hR T hK hpos hm hθ
      (multiplyCLM (root_memLp hR.le T θ (hb n) (hbnd n)) (J n))) l
      (𝓝 (physicalReturn hR T hK hpos hm hθ J0)) := by
  let A n := multiplyCLM (root_memLp hR.le T θ (hb n) (hbnd n))
  have hone : ∀ᵐ z ∂sourceMeasure R T, |(1 : ℝ)| ≤ C :=
    ae_of_all _ (fun _ => by simpa using hC)
  have hn : ∀ n, ‖A n‖ ≤ C^2 := fun n => multiply_norm_bound _ (sq_nonneg C)
    ((SpacetimeRJMeasure.measure_absolutelyContinuous R T θ).ae_le (root_bound hR.le T (hbnd n)))
  have hf : ∀ V, Tendsto (fun n => A n V) l (𝓝 V) := by
    intro V
    have h := root_fixed_test_operator_strong hR.le T θ hb aestronglyMeasurable_const
      hbnd hone hc V
    have he := multiply_eq_id (root_memLp hR.le T θ aestronglyMeasurable_const hone)
      (ae_of_all _ (fun _ => by simp [root]))
    simpa only [he,ContinuousLinearMap.one_apply] using h
  have hs := HilbertOperatorConvergence.strong_on_moving A 1 hn hf hJ
  exact ((physicalDifference hR T hK hpos hm hθ).adjoint.continuous.tendsto J0 |>.comp hs).neg

end
end Resonance.SpacetimePhysicalReturn
