import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Gluing genuine local measure inequalities by a countable disjoint refinement.
There is no finiteness assumption on either measure. -/
open Set MeasureTheory
namespace Resonance.MeasureLocalComparison

theorem restrict_iUnion_le_of_restrict_le {X:Type*} [MeasurableSpace X]
    (μ ν:Measure X) (U:ℕ→Set X) (hU:∀n,MeasurableSet (U n))
    (hle:∀n,μ.restrict (U n)≤ν.restrict (U n)) :
    μ.restrict (⋃n,U n)≤ν.restrict (⋃n,U n) := by
  let V:=disjointed U
  have hV:∀n,MeasurableSet (V n):=MeasurableSet.disjointed hU
  have hVle:∀n,μ.restrict (V n)≤ν.restrict (V n):=by
    intro n
    have h:=Measure.restrict_mono_measure (hle n) (V n)
    have hvu:V n∩U n=V n:=inter_eq_left.mpr (disjointed_le U n)
    simpa only [Measure.restrict_restrict (hV n),
      hvu] using h
  rw [←iUnion_disjointed (f:=U),
    Measure.restrict_iUnion (disjoint_disjointed U) hV,
    Measure.restrict_iUnion (disjoint_disjointed U) hV]
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact ENNReal.tsum_le_tsum (fun n=>hVle n s)

theorem le_of_countable_restrict_le {X:Type*} [MeasurableSpace X]
    (μ ν:Measure X) (U:ℕ→Set X) (hU:∀n,MeasurableSet (U n))
    (hcover:⋃n,U n=univ) (hle:∀n,μ.restrict (U n)≤ν.restrict (U n)) : μ≤ν := by
  simpa only [hcover,Measure.restrict_univ] using restrict_iUnion_le_of_restrict_le μ ν U hU hle

theorem restrict_le_of_locally_restrict_le {X:Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν:Measure X) (T:Set X)
    (hloc:∀x∈T,∃U:Set X,IsOpen U ∧ x∈U ∧ U⊆T ∧ μ.restrict U≤ν.restrict U) :
    μ.restrict T≤ν.restrict T := by
  classical
  by_cases hT:T.Nonempty
  · letI:Nonempty T:=hT.to_subtype
    choose U hU hx hsub hle using (fun x:T=>hloc x x.property)
    have hcover:T⊆⋃x:T,U x:=by
      intro x hxT
      exact mem_iUnion.mpr ⟨⟨x,hxT⟩,hx ⟨x,hxT⟩⟩
    obtain ⟨j,hj⟩:∃j:ℕ→T,T⊆⋃n,U (j n):=
      (HereditarilyLindelofSpace.isLindelof T).indexed_countable_subcover U hU hcover
    have he:⋃n,U (j n)=T:=subset_antisymm (iUnion_subset (fun n=>hsub (j n))) hj
    simpa only [he] using restrict_iUnion_le_of_restrict_le μ ν (fun n=>U (j n))
      (fun n=>(hU (j n)).measurableSet) (fun n=>hle (j n))
  · simp [Set.not_nonempty_iff_eq_empty.mp hT]

theorem le_of_locally_restrict_le {X:Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν:Measure X)
    (hloc:∀x,∃U:Set X,IsOpen U ∧ x∈U ∧ μ.restrict U≤ν.restrict U) : μ≤ν := by
  classical
  by_cases hX:Nonempty X
  · letI:=hX
    choose U hU hx hle using hloc
    have hcover:(univ:Set X)⊆⋃x,U x:=by
      intro x _
      exact mem_iUnion.mpr ⟨x,hx x⟩
    obtain ⟨j,hj⟩:∃j:ℕ→X,(univ:Set X)⊆⋃n,U (j n):=
      isLindelof_univ.indexed_countable_subcover U hU hcover
    exact le_of_countable_restrict_le μ ν (fun n=>U (j n))
      (fun n=>(hU (j n)).measurableSet) (univ_subset_iff.mp hj) (fun n=>hle (j n))
  · haveI:IsEmpty X:=not_nonempty_iff.mp hX
    exact le_of_eq (Subsingleton.elim μ ν)

end Resonance.MeasureLocalComparison
