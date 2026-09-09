import Resonance.SpacetimeDifference
import Resonance.LpFixedTestOperators

/-! The two multiplication operators in the actual current act on the one
reference-frequency source space and the one variable-RJ quartet space.
Bounds and fixed-test convergence are derived from phase-volume data. -/
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace Resonance.SpacetimeMultiplierOperators
noncomputable section
open SpacetimePairing SpacetimeReference SpacetimeRootMultiplier LpOperators

theorem source_memLp {R : ℝ} (hR : 0<R) (T : ℝ) {b : Source→ℝ} {C : ℝ}
    (hb : AEStronglyMeasurable b (sourceMeasure R T))
    (hbound : ∀ᵐz∂sourceMeasure R T,|b z|≤C) : MemLp b ∞ (reference R T) := by
  have hac:reference R T≪sourceMeasure R T:=(reference_volume_equivalent hR T).1
  exact memLp_top_of_bound (hb.mono_ac hac) C (by simpa only [Real.norm_eq_abs] using hac.ae_le hbound)

theorem root_memLp {R : ℝ} (hR : 0≤R) (T : ℝ)
    (θ : Base→Thermodynamics.Parameter) {b : Source→ℝ} {C : ℝ}
    (hb : AEStronglyMeasurable b (sourceMeasure R T))
    (hbound : ∀ᵐz∂sourceMeasure R T,|b z|≤C) :
    MemLp (root b) ∞ (SpacetimeRJMeasure.measure R T θ) := by
  have hac:=SpacetimeRJMeasure.measure_absolutelyContinuous R T θ
  exact memLp_top_of_bound ((root_measurable hR T hb).mono_ac hac) (C^2)
    (by simpa only [Real.norm_eq_abs] using hac.ae_le (root_bound hR T hbound))

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

theorem source_fixed_test_strong {R : ℝ} (hR : 0<R) (T : ℝ)
    {b : ι→Source→ℝ} {d : Source→ℝ} {C : ℝ}
    (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hd : AEStronglyMeasurable d (sourceMeasure R T))
    (hbnd : ∀n,∀ᵐz∂sourceMeasure R T,|b n z|≤C)
    (hdnd : ∀ᵐz∂sourceMeasure R T,|d z|≤C)
    (hconv : TendstoInMeasure (sourceMeasure R T) b l d)
    (V : Space R T) :
    Tendsto (fun n=>multiplyCLM (source_memLp hR T (hb n) (hbnd n)) V) l
      (𝓝 (multiplyCLM (source_memLp hR T hd hdnd) V)) := by
  have hac:reference R T≪sourceMeasure R T:=(reference_volume_equivalent hR T).1
  exact LpFixedTestOperators.fixed_test_strong _ _ (fun n=>hac.ae_le (hbnd n))
    (hac.ae_le hdnd) hac hconv V

theorem root_fixed_test_operator_strong {R : ℝ} (hR : 0≤R) (T : ℝ)
    (θ : Base→Thermodynamics.Parameter)
    {b : ι→Source→ℝ} {d : Source→ℝ} {C : ℝ}
    (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hd : AEStronglyMeasurable d (sourceMeasure R T))
    (hbnd : ∀n,∀ᵐz∂sourceMeasure R T,|b n z|≤C)
    (hdnd : ∀ᵐz∂sourceMeasure R T,|d z|≤C)
    (hconv : TendstoInMeasure (sourceMeasure R T) b l d)
    (V : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)) :
    Tendsto (fun n=>multiplyCLM (root_memLp hR T θ (hb n) (hbnd n)) V) l
      (𝓝 (multiplyCLM (root_memLp hR T θ hd hdnd) V)) := by
  have hac:=SpacetimeRJMeasure.measure_absolutelyContinuous R T θ
  exact LpFixedTestOperators.fixed_test_strong _ _
    (fun n=>hac.ae_le (root_bound hR T (hbnd n)))
    (hac.ae_le (root_bound hR T hdnd)) hac
    (root_tendstoInMeasure hR T hb hconv) V

end
end Resonance.SpacetimeMultiplierOperators
