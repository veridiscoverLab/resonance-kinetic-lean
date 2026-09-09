import Resonance.FiniteSourceLimit
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! An exact finite period-cell compactification, with integrability obtained
from the same weighted whole source and the actual measure-preserving shifts. -/
open Set MeasureTheory
namespace Resonance.FinitePeriodicIntegral
noncomputable section
variable {X E ι : Type*} [MeasurableSpace X] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compactification (μ : Measure X) (e : ι → X ≃ᵐ X)
    (hMP : ∀i,MeasurePreserving (e i) μ μ) {S : Set X} (hS : MeasurableSet S)
    (hd : Pairwise (fun i j=>Disjoint (e i '' S) (e j '' S)))
    (χ : X → ℝ) (f : X → E)
    (hcover : ∀x,χ x≠0→x∈⋃i,e i '' S)
    (hsum : ∀x∈S,∑i,χ (e i x)=1)
    (hperiod : ∀i,∀x∈S,f (e i x)=f x)
    (hi : Integrable (fun x=>χ x • f x) μ) :
    IntegrableOn f S μ ∧ (∫x,χ x • f x ∂μ)=∫x in S,f x ∂μ := by
  classical
  let g : X → E := fun x=>χ x • f x
  let bi : ι → X → E := fun i x=>χ (e i x) • f x
  have hbi : ∀i,IntegrableOn (bi i) S μ := by
    intro i
    have hloc : IntegrableOn (g ∘ e i) S μ :=
      ((hMP i).integrableOn_image (e i).measurableEmbedding).mp hi.integrableOn
    apply hloc.congr
    filter_upwards [ae_restrict_mem hS] with x hx
    simp only [Function.comp_apply,g,bi,hperiod i x hx]
  have heq : ∀x∈S,∑i,bi i x=f x := by
    intro x hx
    simp only [bi,←Finset.sum_smul,hsum x hx,one_smul]
  have hif : IntegrableOn f S μ := by
    apply (integrable_finset_sum Finset.univ (fun i _=>hbi i)).congr
    filter_upwards [ae_restrict_mem hS] with x hx
    exact heq x hx
  refine ⟨hif,?_⟩
  have hz : ∀x∉⋃i,e i '' S,g x=0 := by
    intro x hx
    have hχ : χ x=0 := by by_contra hn; exact hx (hcover x hn)
    simp [g,hχ]
  calc
    _ = ∫x in ⋃i,e i '' S,g x ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ = ∑i,∫x in e i '' S,g x ∂μ := integral_iUnion_fintype
      (fun i=>(e i).measurableEmbedding.measurableSet_image.mpr hS) hd (fun _=>hi.integrableOn)
    _ = ∑i,∫x in S,bi i x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hMP i).setIntegral_image_emb (e i).measurableEmbedding]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hS] with x hx
      simp only [g,bi,hperiod i x hx]
    _ = ∫x in S,∑i,bi i x ∂μ := (integral_finset_sum _ (fun i _=>hbi i)).symm
    _ = _ := integral_congr_ae (by
      filter_upwards [ae_restrict_mem hS] with x hx
      exact heq x hx)

end
end Resonance.FinitePeriodicIntegral
