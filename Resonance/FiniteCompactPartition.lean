import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.Module.BigOperators

/-! A finite partition of an actual compact source, constructed from its open
cover. The exact source sum is global and every piece keeps its chart support. -/
open Set
namespace Resonance.FiniteCompactPartition
noncomputable section
variable {X E ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_source_decomposition {B : X → E} (hB : Continuous B)
    (hK : HasCompactSupport B) (U : ι → Set X) (hU : ∀i,IsOpen (U i))
    (hcover : tsupport B⊆⋃i,U i) :
    ∃ I : Finset ι, ∃ ψ : (↑I) → C(X,ℝ),
      (∀i,tsupport (ψ i)⊆U i) ∧
      (∀i,∀x,ψ i x∈Icc (0:ℝ) 1) ∧
      (∀x,∑i:↑I,ψ i x • B x=B x) ∧
      (∀i,Continuous (fun x=>ψ i x • B x) ∧
        HasCompactSupport (fun x=>ψ i x • B x) ∧
        tsupport (fun x=>ψ i x • B x)⊆U i) := by
  classical
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover U hU hcover
  have hcov : tsupport B⊆⋃i:↑I,U i := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hI hx)
    obtain ⟨hiI,hix⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i,hiI⟩,hix⟩
  obtain ⟨ψ,hsub,_⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space hK
    (fun i:↑I=>U i) (fun i=>hU i) (locallyFinite_of_finite _) hcov
  refine ⟨I,ψ,hsub,fun i x=>⟨ψ.nonneg i x,ψ.le_one i x⟩,?_,?_⟩
  · intro x
    by_cases hx : B x=0
    · simp [hx]
    · have hsum := ψ.sum_eq_one (subset_tsupport B hx)
      have hfin : (∑ᶠi:↑I,ψ i x)=∑i:↑I,ψ i x :=
        finsum_eq_sum_of_support_subset _ (by intro i _; simp)
      rw [hfin] at hsum
      rw [←Finset.sum_smul,hsum,one_smul]
  · intro i
    exact ⟨(ψ i).continuous.smul hB,hK.smul_left,
      (tsupport_smul_subset_left _ _).trans (hsub i)⟩

end
end Resonance.FiniteCompactPartition
