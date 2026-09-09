import Resonance.RegularPointMollifier
import Resonance.RegularCoareaSupport
import Resonance.FiniteCompactPartition
import Resonance.FiniteSourceLimit

/-! The regular compact-source limit is proved by an actual finite partition
of its support, not by assuming a global disintegration or local-to-global axiom. -/
open Set MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
namespace Resonance.CompactRegularMollifier
noncomputable section
open LinearSurfaceArea RegularGraphCoarea RegularCoareaSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem compact_regular_limit {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀p,HasFDerivAt F (innerSL ℝ (g p)) p) (hFC : ContDiff ℝ 1 F)
    (hg : Measurable g) (hc : 0<c) {B : A → E}
    (hB : Continuous B) (hK : HasCompactSupport B)
    (hreg : ∀p∈tsupport B,g p≠0) (ρ : ℝ → ℝ → ℝ)
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀x,0≤ρ η x)
    (hmass : ∀η,0<η→∫x,ρ η x=1)
    (hsupport : ∀η,0<η→∀x,ρ η x≠0→|x|≤η) :
    (∀η,0<η→Integrable (fun p=>ρ η (F p) • B p)) ∧
    Integrable B (regularMeasure F g c) ∧
    Tendsto (fun η=>c⁻¹ • ∫p,ρ η (F p) • B p)
      (𝓝[>]0) (𝓝 (∫p,B p ∂regularMeasure F g c)) := by
  classical
  have hloc := fun p:tsupport B=>
    RegularPointMollifier.every_regular_point (E:=E) hF hFC hg hc p (hreg p p.property)
  choose U hU hpoint hlim using hloc
  have hcover : tsupport B⊆⋃p:tsupport B,U p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hpoint ⟨p,hp⟩⟩
  obtain ⟨I,ψ,hψ,_,hsum,hpieces⟩ :=
    FiniteCompactPartition.finite_source_decomposition hB hK U hU hcover
  let b : (↑I) → A → E := fun i x=>ψ i x • B x
  have hl : ∀i:↑I,
      (∀η,0<η→IntegrableOn (fun p=>ρ η (F p) • b i p) (U i)) ∧
      IntegrableOn (b i) (U i∩{p|F p=0}) (regularMeasure F g c) ∧
      Tendsto (fun η=>c⁻¹ • ∫p in U i,ρ η (F p) • b i p) (𝓝[>]0)
        (𝓝 (∫p in U i∩{p|F p=0},b i p ∂regularMeasure F g c)) := by
    intro i
    exact hlim i (b i) (hpieces i).1 (hpieces i).2.1 (hpieces i).2.2
      ρ hρ hpos hmass hsupport
  have hbzero : ∀i:↑I,∀x,x∉U i→b i x=0 := by
    intro i x hx
    by_contra hn
    exact hx ((hpieces i).2.2 (subset_tsupport (b i) hn))
  have hv : ∀η,0<η→∀i:↑I,Integrable (fun x=>ρ η (F x) • b i x) := by
    intro η hη i
    exact ((hl i).1 η hη).integrable_of_forall_notMem_eq_zero
      (fun x hx=>by rw [hbzero i x hx,smul_zero])
  have hs : ∀i:↑I,Integrable (b i) (regularMeasure F g c) ∧
      (∫x in U i∩{x|F x=0},b i x ∂regularMeasure F g c)=
        ∫x,b i x ∂regularMeasure F g c := by
    intro i
    exact globalize_source (zero_energy_ae hFC.continuous.measurable hg c)
      (hpieces i).2.2 (hl i).2.1
  have he : ∀i:↑I,∀η,(∫x in U i,ρ η (F x) • b i x)=∫x,ρ η (F x) • b i x := by
    intro i η
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx=>by rw [hbzero i x hx,smul_zero])
  have ht : ∀i:↑I,Tendsto (fun η=>c⁻¹ • ∫x,ρ η (F x) • b i x) (𝓝[>]0)
      (𝓝 (∫x,b i x ∂regularMeasure F g c)) := by
    intro i
    have ht := (hl i).2.2
    rw [(hs i).2] at ht
    simp_rw [he i] at ht
    exact ht
  exact FiniteSourceLimit.common_integral_limit volume (regularMeasure F g c) B b hsum
    (fun η x=>ρ η (F x)) (c⁻¹) hv (fun i=>(hs i).1) ht

end
end Resonance.CompactRegularMollifier
