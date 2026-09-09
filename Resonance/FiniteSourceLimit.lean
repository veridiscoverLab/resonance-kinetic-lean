import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators

/-! Finite exact source decompositions commute with a common integral limit.
The measures and the whole source remain fixed across all pieces. -/
open MeasureTheory Filter
open scoped Topology
namespace Resonance.FiniteSourceLimit
noncomputable section
variable {X E ι : Type*} [MeasurableSpace X] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem common_integral_limit (μ ν : Measure X) (B : X → E) (b : ι → X → E)
    (hsum : ∀x,∑i,b i x=B x) (ρ : ℝ → X → ℝ) (c : ℝ)
    (hv : ∀η,0<η→∀i,Integrable (fun x=>ρ η x • b i x) μ)
    (hs : ∀i,Integrable (b i) ν)
    (ht : ∀i,Tendsto (fun η=>c • ∫x,ρ η x • b i x ∂μ) (𝓝[>]0) (𝓝 (∫x,b i x ∂ν))) :
    (∀η,0<η→Integrable (fun x=>ρ η x • B x) μ) ∧ Integrable B ν ∧
      Tendsto (fun η=>c • ∫x,ρ η x • B x ∂μ) (𝓝[>]0) (𝓝 (∫x,B x ∂ν)) := by
  classical
  have he : (fun x=>∑i,b i x)=B := funext hsum
  have hiB : Integrable B ν := by
    rw [←he]
    exact integrable_finset_sum _ (fun i _=>hs i)
  have hev : ∀η,(fun x=>∑i,ρ η x • b i x)=fun x=>ρ η x • B x := by
    intro η
    ext x
    rw [←Finset.smul_sum,hsum]
  have hiv : ∀η,0<η→Integrable (fun x=>ρ η x • B x) μ := by
    intro η hη
    rw [←hev η]
    exact integrable_finset_sum _ (fun i _=>hv η hη i)
  refine ⟨hiv,hiB,?_⟩
  have hvsum : ∀η,0<η→(∑i,c • ∫x,ρ η x • b i x ∂μ)=c • ∫x,ρ η x • B x ∂μ := by
    intro η hη
    rw [←Finset.smul_sum,←integral_finset_sum _ (fun i _=>hv η hη i),hev η]
  have hssum : (∑i,∫x,b i x ∂ν)=∫x,B x ∂ν := by
    rw [←integral_finset_sum _ (fun i _=>hs i),he]
  have htSum := tendsto_finset_sum Finset.univ (fun i _=>ht i)
  rw [hssum] at htSum
  apply htSum.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact hvsum η hη

end
end Resonance.FiniteSourceLimit
