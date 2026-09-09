import Resonance.PeriodicHatPartition

/-! Compact support and actual finite translated-cell coverage of the period
hat. The original half-open cells are retained, including their seams. -/
open Set MeasureTheory
namespace Resonance.PeriodicHatCells
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCompactLocalization PeriodicHatPartition

theorem weight_support_bound {k : Ambient} (hk : weight k≠0) (j : Fin 3) : |k j|<period := by
  have hj : hat (k j)≠0 := (Finset.prod_ne_zero_iff.mp hk) j (Finset.mem_univ j)
  exact lt_of_not_ge (fun h=>hj (hat_eq_zero_of_le h))

theorem weight_hasCompactSupport : HasCompactSupport weight := by
  let K : Set (Fin 3 → ℝ) := Set.univ.pi (fun _=>Icc (-period) period)
  have hK : IsCompact K := isCompact_univ_pi (fun _=>isCompact_Icc)
  apply HasCompactSupport.of_support_subset_isCompact
    (hK.image (PiLp.continuous_toLp 2 (fun _ : Fin 3=>ℝ)))
  intro k hk
  refine ⟨WithLp.ofLp k,?_,by rfl⟩
  intro j _
  exact abs_le.mp (weight_support_bound hk j).le

theorem translatedCell_coordinates (i : Index) (k : Ambient) :
    k∈translatedCell (winding i) ↔ ∀j:Fin 3,k j+(i j:ℝ)*period∈Ico 0 period := by
  constructor
  · rintro ⟨q,hq,heq⟩ j
    have he := congrArg (fun p : Ambient=>p j) heq
    simp only [translation_apply,PiLp.add_apply,latticeShift,winding] at he
    push_cast at he
    have he' : k j+(i j:ℝ)*period=q j := by linarith
    rw [he']
    exact hq j
  · intro hk
    let q : Ambient := WithLp.toLp 2 (fun j=>k j+(i j:ℝ)*period)
    refine ⟨q,hk,?_⟩
    ext j
    simp [translation_apply,PiLp.add_apply,latticeShift,winding,q]

theorem weight_support_covered {k : Ambient} (hk : weight k≠0) :
    k∈⋃i:Index,translatedCell (winding i) := by
  classical
  let i : Index := fun j=>if k j<0 then 1 else 0
  refine mem_iUnion.mpr ⟨i,(translatedCell_coordinates i k).mpr ?_⟩
  intro j
  have hb := abs_lt.mp (weight_support_bound hk j)
  by_cases hj : k j<0
  · simp only [i,if_pos hj,Fin.val_one,Nat.cast_one,one_mul]
    exact ⟨by linarith,by linarith⟩
  · simp only [i,if_neg hj,Fin.val_zero,Nat.cast_zero,zero_mul,add_zero]
    exact ⟨le_of_not_gt hj,hb.2⟩

theorem translatedCells_pairwise_disjoint : Pairwise
    (fun i l : Index=>Disjoint (translatedCell (winding i)) (translatedCell (winding l))) := by
  intro i l hil
  rw [disjoint_left]
  intro k hki hkl
  have hi := (translatedCell_coordinates i k).mp hki
  have hl := (translatedCell_coordinates l k).mp hkl
  have hex : ∃j,i j≠l j := by
    by_contra h
    push Not at h
    exact hil (funext h)
  obtain ⟨j,hj⟩ := hex
  have hi' := hi j
  have hl' := hl j
  generalize hiV : i j=a at hj hi'
  generalize hlV : l j=b at hj hl'
  fin_cases a <;> fin_cases b <;> simp_all
  all_goals linarith [hi'.1,hi'.2,hl'.1,hl'.2]

end
end Resonance.PeriodicHatCells
