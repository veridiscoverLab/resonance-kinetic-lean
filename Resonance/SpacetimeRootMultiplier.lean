import Resonance.SpacetimePairing

/-! A single subsequence and a single time-space-quartet variable are used
for all four factors. Fixed tests may depend on the entire joint variable;
they are not required to be single-leg or separable tests. -/
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
namespace Resonance.SpacetimeRootMultiplier
noncomputable section
open SpacetimePairing

def root (b : Source→ℝ) (p : Joint) : ℝ := Real.sqrt (∏i:Fin 4,b (leg i p))

theorem root_measurable {R : ℝ} (hR : 0≤R) (T : ℝ) {b : Source→ℝ}
    (hb : AEStronglyMeasurable b (sourceMeasure R T)) :
    AEStronglyMeasurable (root b) (jointMeasure R T) := by
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  exact Finset.aestronglyMeasurable_fun_prod _ (fun i _=>
    hb.comp_quasiMeasurePreserving (leg_quasiMeasurePreserving hR T i))

theorem root_tendstoInMeasure {R : ℝ} (hR : 0≤R) (T : ℝ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {b : ι→Source→ℝ} {c : Source→ℝ}
    (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hconv : TendstoInMeasure (sourceMeasure R T) b l c) :
    TendstoInMeasure (jointMeasure R T) (fun n=>root (b n)) l (root c) := by
  letI := jointMeasure_finite hR T
  intro ε hε
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,_,hlim⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  have hlegs : ∀ᵐp∂jointMeasure R T,∀i:Fin 4,
      Tendsto (fun n=>b (ns (ms n)) (leg i p)) atTop (𝓝 (c (leg i p))) := by
    rw [ae_all_iff]
    intro i
    exact (leg_quasiMeasurePreserving hR T i).ae hlim
  have hp : ∀ᵐp∂jointMeasure R T,
      Tendsto (fun n=>root (b (ns (ms n))) p) atTop (𝓝 (root c p)) := by
    filter_upwards [hlegs] with p hp
    exact Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_finset_prod Finset.univ (fun i _=>hp i))
  exact (tendstoInMeasure_of_tendsto_ae
    (fun n=>root_measurable hR T (hb (ns (ms n)))) hp) ε hε

theorem root_bound {R : ℝ} (hR : 0≤R) (T : ℝ) {b : Source→ℝ} {C : ℝ}
    (hb : ∀ᵐz∂sourceMeasure R T,|b z|≤C) :
    ∀ᵐp∂jointMeasure R T,|root b p|≤C^2 := by
  have hlegs : ∀ᵐp∂jointMeasure R T,∀i:Fin 4,|b (leg i p)|≤C := by
    rw [ae_all_iff]
    intro i
    exact (leg_quasiMeasurePreserving hR T i).ae hb
  filter_upwards [hlegs] with p hp
  have hprod : |∏i:Fin 4,b (leg i p)|≤C^4 := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod (fun i (_:i∈(Finset.univ:Finset (Fin 4)))=>
      abs_nonneg (b (leg i p))) (fun i _=>hp i)
  have h : (∏i:Fin 4,b (leg i p))≤(C^2)^2 :=
    (le_abs_self _).trans (by nlinarith [hprod])
  change |Real.sqrt _|≤_
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (sq_nonneg C)] using Real.sqrt_le_sqrt h

theorem root_square {R : ℝ} (hR : 0≤R) (T : ℝ) {b : Source→ℝ}
    (hb : ∀ᵐz∂sourceMeasure R T,0≤b z) :
    ∀ᵐp∂jointMeasure R T,(root b p)^2=∏i:Fin 4,b (leg i p) := by
  have hlegs : ∀ᵐp∂jointMeasure R T,∀i:Fin 4,0≤b (leg i p) := by
    rw [ae_all_iff]
    intro i
    exact (leg_quasiMeasurePreserving hR T i).ae hb
  filter_upwards [hlegs] with p hp
  exact Real.sq_sqrt (Finset.prod_nonneg (fun i _=>hp i))

theorem root_fixed_test_strong {R : ℝ} (hR : 0≤R) (T : ℝ)
    {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} [l.IsCountablyGenerated] {σ : Measure Joint}
    (hσ : σ≪jointMeasure R T) {b : ι→Source→ℝ} {c : Source→ℝ}
    {V : Joint→F} {C : ℝ}
    (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hc : AEStronglyMeasurable c (sourceMeasure R T))
    (hbnd : ∀n,∀ᵐz∂sourceMeasure R T,|b n z|≤C)
    (hcnd : ∀ᵐz∂sourceMeasure R T,|c z|≤C)
    (hconv : TendstoInMeasure (sourceMeasure R T) b l c) (hV : MemLp V 2 σ) :
    ∃G:ι→Lp F 2 σ,(∀n,G n=ᵐ[σ](fun p=>(root (b n) p-root c p) • V p)) ∧
      Tendsto G l (𝓝 0) :=
  FixedMultiplier.fixed_multiplier_strong hσ (root_tendstoInMeasure hR T hb hconv)
    (fun n=>(root_measurable hR T (hb n)).mono_ac hσ)
    ((root_measurable hR T hc).mono_ac hσ)
    (fun n=>hσ.ae_le (root_bound hR T (hbnd n)))
    (hσ.ae_le (root_bound hR T hcnd)) hV

end
end Resonance.SpacetimeRootMultiplier
