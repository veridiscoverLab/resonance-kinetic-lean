import Resonance.FiniteSourceLimit

/-! Finite exact source partitions with eventual integrability. Pieces away
from the zero energy set need integrability only for sufficiently small kernels. -/
open MeasureTheory Filter
open scoped Topology
namespace Resonance.FiniteEventualSourceLimit
noncomputable section
variable {X E ι : Type*} [MeasurableSpace X] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem common_integral_limit (μ ν : Measure X) (B : X → E) (b : ι → X → E)
    (hsum : ∀x,∑i,b i x=B x) (ρ : ℝ → X → ℝ) (c : ℝ)
    (hv : ∀i,∀ᶠη in 𝓝[>]0,Integrable (fun x=>ρ η x • b i x) μ)
    (hs : ∀i,Integrable (b i) ν)
    (ht : ∀i,Tendsto (fun η=>c • ∫x,ρ η x • b i x ∂μ) (𝓝[>]0) (𝓝 (∫x,b i x ∂ν))) :
    (∀ᶠη in 𝓝[>]0,Integrable (fun x=>ρ η x • B x) μ) ∧ Integrable B ν ∧
      Tendsto (fun η=>c • ∫x,ρ η x • B x ∂μ) (𝓝[>]0) (𝓝 (∫x,B x ∂ν)) := by
  classical
  have hall : ∀ᶠη in 𝓝[>]0,∀i,Integrable (fun x=>ρ η x • b i x) μ := eventually_all.mpr hv
  have he : (fun x=>∑i,b i x)=B := funext hsum
  have hev : ∀η,(fun x=>∑i,ρ η x • b i x)=fun x=>ρ η x • B x := by
    intro η
    funext x
    rw [←Finset.smul_sum,hsum]
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hall] with η hη
    rw [←hev η]
    exact integrable_finset_sum _ (fun i _=>hη i)
  · rw [←he]
    exact integrable_finset_sum _ (fun i _=>hs i)
  · have hssum : (∑i,∫x,b i x ∂ν)=∫x,B x ∂ν := by
      rw [←integral_finset_sum _ (fun i _=>hs i),he]
    have htSum := tendsto_finset_sum Finset.univ (fun i _=>ht i)
    rw [hssum] at htSum
    apply htSum.congr'
    filter_upwards [hall] with η hη
    rw [←Finset.smul_sum,←integral_finset_sum _ (fun i _=>hη i),hev η]

end
end Resonance.FiniteEventualSourceLimit
