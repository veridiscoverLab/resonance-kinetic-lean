import Resonance.SpacetimeCurrentConvergence
import Resonance.SpacetimeRootLower
import Resonance.HilbertEntropyConvergence

/-! Norm equality is derived from weak convergence and the nonnegative
terminal entropy budget on the entire common window. The source weak limit
and entropy-work limit remain explicit front-end obligations; the entropy
equality itself has the actual realization in SpacetimeEntropyBalance. -/
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace Resonance.SpacetimeEntropyStrong
noncomputable section
open SpacetimePairing SpacetimeReference SpacetimeDifference
open SpacetimeMultiplierOperators LpOperators LpFixedTestOperators
variable {R : ℝ} (hR : 0 < R) (T : ℝ) {K : Set Thermodynamics.Parameter}
  (hK : IsCompact K) (hpos : K ⊆ Thermodynamics.positiveDomain R)
  {θ : Base → Thermodynamics.Parameter} (hm : Measurable θ)
  (hθ : ∀ᵐ a ∂baseMeasure T, θ a ∈ K)
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
  {b : ι → Source → ℝ} {C : ℝ} (hC : 1 ≤ C)
  (hb : ∀ n, AEStronglyMeasurable (b n) (sourceMeasure R T))
  (hbnd : ∀ n, ∀ᵐ z ∂sourceMeasure R T, |b n z| ≤ C)

def jointCurrent (n : ι) (y : Space R T) : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ) :=
  multiplyCLM (root_memLp hR.le T θ (hb n) (hbnd n))
    (physicalDifference hR T hK hpos hm hθ y)

include hC in
theorem weak_joint_current
    (hc : TendstoInMeasure (sourceMeasure R T) b l (fun _ => 1))
    {y : ι → Space R T} {u : Space R T} {Cy : ℝ} (hy : ∀ n, ‖y n‖ ≤ Cy)
    (hw : ∀ v : Space R T, Tendsto (fun n => inner ℝ (y n) v) l (𝓝 (inner ℝ u v))) :
    ∀ V : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ),
      Tendsto (fun n => inner ℝ (jointCurrent hR T hK hpos hm hθ hb hbnd n (y n)) V) l
        (𝓝 (inner ℝ (physicalDifference hR T hK hpos hm hθ u) V)) := by
  have hdm (n : ι) : AEStronglyMeasurable (fun _ : Source => (1 : ℝ)) (sourceMeasure R T) :=
    aestronglyMeasurable_const
  have hdb (n : ι) : ∀ᵐ z ∂sourceMeasure R T, |(1 : ℝ)| ≤ C :=
    ae_of_all _ (fun _ => by simpa using hC)
  have hdconv : TendstoInMeasure (sourceMeasure R T) (fun _ : ι => fun _ : Source => (1 : ℝ))
      l (fun _ => 1) := by
    intro ε hε
    simpa only [edist_self,not_le_of_gt hε,setOf_false,measure_empty] using
      (tendsto_const_nhds (x := (0 : ℝ≥0∞)) (f := l))
  have h := SpacetimeCurrentConvergence.weak_current hR T hK hpos hm hθ hC hb hdm
    hbnd hdb hc hdconv hy hw
  have hid (n : ι) := multiply_eq_id (source_memLp hR T (hdm n) (hdb n))
    (ae_of_all _ (fun _ => rfl))
  have heq (n : ι) : SpacetimeCurrentConvergence.current hR T hK hpos hm hθ
      hb hdm hbnd hdb n (y n) = jointCurrent hR T hK hpos hm hθ hb hbnd n (y n) := by
    unfold SpacetimeCurrentConvergence.current jointCurrent
    erw [hid n]
    rfl
  simpa only [heq] using h

include hC in
theorem whole_current_and_quotient_strong
    (hc : TendstoInMeasure (sourceMeasure R T) b l (fun _ => 1))
    {m : ℝ} (hm0 : 0 < m) (hl : ∀ n, ∀ᵐ z ∂sourceMeasure R T, m ≤ b n z)
    {y : ι → Space R T} {u : Space R T} {Cy : ℝ} (hy : ∀ n, ‖y n‖ ≤ Cy)
    (hw : ∀ v : Space R T, Tendsto (fun n => inner ℝ (y n) v) l (𝓝 (inner ℝ u v)))
    {W H : ι → ℝ}
    (hW : Tendsto W l (𝓝 (‖physicalDifference hR T hK hpos hm hθ u‖ ^ 2)))
    (hH : ∀ n, 0 ≤ H n)
    (he : ∀ n, ‖jointCurrent hR T hK hpos hm hθ hb hbnd n (y n)‖ ^ 2 + H n = W n) :
    Tendsto (fun n => jointCurrent hR T hK hpos hm hθ hb hbnd n (y n)) l
        (𝓝 (physicalDifference hR T hK hpos hm hθ u)) ∧
      Tendsto (fun n => physicalDifference hR T hK hpos hm hθ (y n)) l
        (𝓝 (physicalDifference hR T hK hpos hm hθ u)) ∧ Tendsto H l (𝓝 0) := by
  obtain ⟨hs,hh⟩ := HilbertEntropyConvergence.strong_and_terminal_of_entropy_equality
    (weak_joint_current hR T hK hpos hm hθ hC hb hbnd hc hy hw) hW hH he
  refine ⟨hs,?_,hh⟩
  exact SpacetimeRootLower.remove_root_multiplier hR T θ hm0 hC hb hl hbnd hc hs

end
end Resonance.SpacetimeEntropyStrong
