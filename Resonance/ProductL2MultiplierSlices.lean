import Resonance.ProductL2Slices
import Resonance.LpOperators

/-! Slice the one actual multiplication operator. Exceptional sections are
discarded only after the product L-infinity hypothesis proves them null. -/
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.ProductL2MultiplierSlices
noncomputable section
open ProductL2Slices LpOperators
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
theorem coefficient_memLp_ae {w : A×B→ℝ} (hw : MemLp w ∞ (μ.prod ν)) :
    ∀ᵐa∂μ,MemLp (fun b=>w (a,b)) ∞ ν := by
  filter_upwards [hw.aestronglyMeasurable.prodMk_left,
    ae_ae_of_ae_prod (multiplier_ae_bound hw)] with a hm hb
  exact memLp_top_of_bound hm (multiplierNorm w (μ.prod ν)) hb

def fiberMultiplier (w : A×B→ℝ) (a : A) : Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 ν := by
  classical
  exact if h:MemLp (fun b=>w (a,b)) ∞ ν then multiplyCLM h else 0

theorem multiply_slice_ae {w : A×B→ℝ} (hw : MemLp w ∞ (μ.prod ν))
    (u : Lp ℝ 2 (μ.prod ν)) :
    ∀ᵐa∂μ,slice (multiplyCLM hw u) a=fiberMultiplier w a (slice u a) := by
  filter_upwards [coefficient_memLp_ae hw,slice_ae (multiplyCLM hw u),slice_ae u,
    ae_ae_of_ae_prod (multiply_ae hw u)] with a ha hmul hu hprod
  simp only [fiberMultiplier,dif_pos ha]
  apply Lp.ext
  filter_upwards [hmul,hu,hprod,multiply_ae ha (slice u a)] with b hb hu hp hout
  change slice (multiplyCLM hw u) a b=multiply ha (slice u a) b
  rw [hb,hout,hu]
  exact hp

theorem sub_identity_slice_ae {w : A×B→ℝ} (hw : MemLp w ∞ (μ.prod ν))
    (u : Lp ℝ 2 (μ.prod ν)) :
    ∀ᵐa∂μ,slice ((multiplyCLM hw-1) u) a=(fiberMultiplier w a-1) (slice u a) := by
  filter_upwards [slice_sub_ae (multiplyCLM hw u) u,multiply_slice_ae hw u]
    with a hsub hmul
  change slice (multiplyCLM hw u-u) a=fiberMultiplier w a (slice u a)-slice u a
  rw [hsub,hmul]

end
end Resonance.ProductL2MultiplierSlices
