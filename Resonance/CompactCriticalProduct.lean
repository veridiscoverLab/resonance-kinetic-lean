import Resonance.CriticalProductIntegrability
import Mathlib.Topology.Algebra.Support

/-! Whole compact source at the three-factor critical energy -b(x)q.
Finiteness of the parameter measure follows from the actual compact support. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CompactCriticalProduct
noncomputable section
variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [SFinite μ]

def parameterSupport (A : X × ℝ → E) : Set X := Prod.fst '' tsupport A

omit [MeasurableSpace X] [BorelSpace X] [T2Space X] [SecondCountableTopology X]
    [NormedSpace ℝ E] [CompleteSpace E] in
theorem parameterSupport_compact {A : X × ℝ → E} (hK : HasCompactSupport A) :
    IsCompact (parameterSupport A) := hK.image continuous_fst

omit [MeasurableSpace X] [BorelSpace X] [T2Space X] [SecondCountableTopology X]
    [NormedSpace ℝ E] [CompleteSpace E] in
theorem source_zero_off_parameter {A : X × ℝ → E} {x : X}
    (hx : x∉parameterSupport A) (q : ℝ) : A (x,q)=0 := by
  by_contra hn
  exact hx ⟨(x,q),subset_tsupport A hn,rfl⟩

omit [T2Space X] [CompleteSpace E] in
theorem complete_integrable {A : X × ℝ → E} (hc : Continuous A)
    (hK : HasCompactSupport A) {ρ : ℝ → ℝ} (hm : Measurable ρ)
    (hρ : Integrable ρ) (hpos : ∀q,0≤ρ q) (hmass : ∫q,ρ q=1)
    (b : X → ℝ) (hb : Measurable b) :
    Integrable (fun p : X × ℝ=>b p.1 • (ρ (-b p.1*p.2) • A p)) (μ.prod volume) := by
  let K := parameterSupport A
  have hKc : IsCompact K := parameterSupport_compact hK
  letI : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hKc.measure_lt_top (μ:=μ)⟩
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuous hc
  have hi := CriticalProductIntegrability.complete_joint_integrable (μ.restrict K)
    hm hρ hpos hmass b hb A hc.stronglyMeasurable (le_max_left 0 C)
    (fun x q=>(hC (x,q)).trans (le_max_right 0 C))
  rw [Measure.restrict_prod_eq_prod_univ] at hi
  have hiOn : IntegrableOn (fun p : X × ℝ=>b p.1 • (ρ (-b p.1*p.2) • A p))
      (K ×ˢ univ) (μ.prod volume) := hi
  apply hiOn.integrable_of_forall_notMem_eq_zero
  intro p hp
  have hz : A p=0 := source_zero_off_parameter (fun h=>hp ⟨h,mem_univ _⟩) p.2
  simp [hz]

omit [T2Space X] [CompleteSpace E] in
theorem complete_integral (b : X → ℝ) (hb : Measurable b)
    {A : X × ℝ → E} (hc : Continuous A) (hK : HasCompactSupport A)
    {ρ : ℝ → ℝ} (hm : Measurable ρ) (hρ : Integrable ρ)
    (hpos : ∀q,0≤ρ q) (hmass : ∫q,ρ q=1) :
    (∫p : X × ℝ,b p.1 • (ρ (-b p.1*p.2) • A p) ∂μ.prod volume)=
      ∫x,b x • (∫q,ρ (-b x*q) • A (x,q)) ∂μ := by
  rw [integral_prod _ (complete_integrable μ hc hK hm hρ hpos hmass b hb)]
  congr 1
  funext x
  exact integral_smul (b x) _

omit [T2Space X] in
theorem complete_tendsto {A : X × ℝ → E} (hc : Continuous A)
    (hK : HasCompactSupport A) (b : X → ℝ) (hb : Measurable b)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    Tendsto (fun η=>∫p : X × ℝ,b p.1 • (ρ η (-b p.1*p.2) • A p) ∂μ.prod volume)
      (𝓝[>]0) (𝓝 (∫x,(b x/|b x|) • A (x,0) ∂μ)) := by
  let K := parameterSupport A
  have hKc : IsCompact K := parameterSupport_compact hK
  letI : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hKc.measure_lt_top (μ:=μ)⟩
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuous hc
  have ht := CriticalProductKernel.complete_linear_integral_tendsto (μ.restrict K)
    ρ hm hρ hpos hmass hs b hb A hc.stronglyMeasurable
    (fun x=>(hc.comp (continuous_const.prodMk continuous_id)).continuousAt)
    (le_max_left 0 C) (fun x q=>(hC (x,q)).trans (le_max_right 0 C))
  have hz : ∀x∉K,∀q,A (x,q)=0 := fun x hx q=>source_zero_off_parameter hx q
  have he : ∀η,(∫x,b x • (∫q,ρ η (-b x*q) • A (x,q)) ∂μ.restrict K)=
      ∫x,b x • (∫q,ρ η (-b x*q) • A (x,q)) ∂μ := by
    intro η
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [hz x hx]
  have he0 : (∫x,(b x/|b x|) • A (x,0) ∂μ.restrict K)=
      ∫x,(b x/|b x|) • A (x,0) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [hz x hx]
  simp only [he,he0] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (complete_integral μ b hb hc hK (hm η hη) (hρ η hη) (hpos η hη) (hmass η hη)).symm

end
end Resonance.CompactCriticalProduct
