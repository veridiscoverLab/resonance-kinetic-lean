import Resonance.RegularGraphCoarea

/-! Exact zero-energy support of the original coarea, and legal removal of a
chart restriction for sources supported in that same chart. -/
open Set MeasureTheory
namespace Resonance.RegularCoareaSupport
noncomputable section
open LinearSurfaceArea RegularGraphCoarea

theorem zero_energy_ae {F : A → ℝ} {g : A → A} (hF : Measurable F)
    (hg : Measurable g) (c : ℝ) : ∀ᵐp ∂regularMeasure F g c,F p=0 := by
  have hs : MeasurableSet {p | F p=0 ∧ g p≠0} :=
    (hF (measurableSet_singleton 0)).inter (hg (measurableSet_singleton 0)).compl
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem hs] with p hp
  exact hp.1

theorem globalize_source {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} {F : A → ℝ} (hμ : ∀ᵐp ∂μ,F p=0)
    {B : A → E} {S : Set A} (hS : tsupport B⊆S)
    (hi : IntegrableOn B (S∩{p|F p=0}) μ) :
    Integrable B μ ∧ (∫p in S∩{p|F p=0},B p ∂μ)=∫p,B p ∂μ := by
  have hz : ∀ᵐp ∂μ,p∉S∩{p|F p=0}→B p=0 := by
    filter_upwards [hμ] with p hp hn
    by_contra hB
    exact hn ⟨hS (subset_tsupport B hB),hp⟩
  exact ⟨hi.integrable_of_ae_notMem_eq_zero hz,setIntegral_eq_integral_of_ae_compl_eq_zero hz⟩

end
end Resonance.RegularCoareaSupport
