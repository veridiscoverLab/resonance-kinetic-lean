import Resonance.MarkedQuartetOperator

/-! Simultaneous relabelling of observed and marked legs. One modulus
controls all twelve ordered off-diagonal readers and all four marks. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.AllMarkedQuartetReaders
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open CornerPairTruncation MarkedQuartetPairKernel MarkedQuartetOperator
set_option maxHeartbeats 1800000

theorem marked_relabel (R : ℝ) (θ : Thermodynamics.Parameter)
    (S : FourMomenta→FourMomenta)
    (hS : MeasurePreserving S (jointMeasure R θ) (jointMeasure R θ))
    {i j l i' j' l' : Fin 4} (hi : ∀q,S q i=q i') (hj : ∀q,S q j=q j')
    (hl : ∀q,S q l=q l') (η : ℝ) :
    markedOperator R θ i j l η=markedOperator R θ i' j' l' η := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [actual_marked_pairing,actual_marked_pairing]
  calc
    _=∫q,cut R η (q l)*u (q j)*v (q i)∂(jointMeasure R θ).map S := by rw [hS.map_eq]
    _=∫q,cut R η (S q l)*u (S q j)*v (S q i)∂jointMeasure R θ :=
      integral_map hS.measurable.aemeasurable (by
        rw [hS.map_eq]
        exact (actual_marked_integrable R θ i j l η u v).aestronglyMeasurable)
    _=_ := by simp only [hi,hj,hl]

def incomingIndex (i : Fin 4) : Fin 4:=![1,0,2,3] i
def outgoingIndex (i : Fin 4) : Fin 4:=![0,1,3,2] i
def pairsIndex (i : Fin 4) : Fin 4:=![2,3,0,1] i

theorem marked_incoming (R : ℝ) (θ : Thermodynamics.Parameter) (i j l : Fin 4) (η : ℝ) :
    markedOperator R θ i j l η=
      markedOperator R θ (incomingIndex i) (incomingIndex j) (incomingIndex l) η :=
  marked_relabel R θ swapIncomingK (incoming_preserves_joint R θ)
    (fun _=>by fin_cases i <;> rfl) (fun _=>by fin_cases j <;> rfl)
    (fun _=>by fin_cases l <;> rfl) η

theorem marked_outgoing (R : ℝ) (θ : Thermodynamics.Parameter) (i j l : Fin 4) (η : ℝ) :
    markedOperator R θ i j l η=
      markedOperator R θ (outgoingIndex i) (outgoingIndex j) (outgoingIndex l) η :=
  marked_relabel R θ swapOutgoingK (outgoing_preserves_joint R θ)
    (fun _=>by fin_cases i <;> rfl) (fun _=>by fin_cases j <;> rfl)
    (fun _=>by fin_cases l <;> rfl) η

theorem marked_pairs (R : ℝ) (θ : Thermodynamics.Parameter) (i j l : Fin 4) (η : ℝ) :
    markedOperator R θ i j l η=
      markedOperator R θ (pairsIndex i) (pairsIndex j) (pairsIndex l) η :=
  marked_relabel R θ swapPairsK (pairs_preserves_joint R θ)
    (fun _=>by fin_cases i <;> rfl) (fun _=>by fin_cases j <;> rfl)
    (fun _=>by fin_cases l <;> rfl) η

theorem actual_all_marked_choice (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j l : Fin 4) (hij : i≠j) :
    ∃b l',∀η,markedOperator R θ i j l η=markedOperator R θ 0 (pairLeg b) l' η := by
  have hi := marked_incoming R θ
  have ho := marked_outgoing R θ
  have hp := marked_pairs R θ
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨true,l,fun _=>rfl⟩
  · exact ⟨false,l,fun _=>rfl⟩
  · exact ⟨false,outgoingIndex l,fun η=>by simpa [outgoingIndex,pairLeg] using ho 0 3 l η⟩
  · exact ⟨true,incomingIndex l,fun η=>by simpa [incomingIndex,pairLeg] using hi 1 0 l η⟩
  · exact (hij rfl).elim
  · exact ⟨false,incomingIndex l,fun η=>by simpa [incomingIndex,pairLeg] using hi 1 2 l η⟩
  · refine ⟨false,outgoingIndex (incomingIndex l),fun η=>?_⟩
    exact (hi 1 3 l η).trans (ho 0 3 (incomingIndex l) η)
  · exact ⟨false,pairsIndex l,fun η=>by simpa [pairsIndex,pairLeg] using hp 2 0 l η⟩
  · refine ⟨false,pairsIndex (incomingIndex l),fun η=>?_⟩
    exact (hi 2 1 l η).trans (hp 2 0 (incomingIndex l) η)
  · exact (hij rfl).elim
  · exact ⟨true,pairsIndex l,fun η=>by simpa [pairsIndex,pairLeg] using hp 2 3 l η⟩
  · refine ⟨false,pairsIndex (outgoingIndex l),fun η=>?_⟩
    exact (ho 3 0 l η).trans (hp 2 0 (outgoingIndex l) η)
  · refine ⟨false,pairsIndex (incomingIndex (outgoingIndex l)),fun η=>?_⟩
    exact (ho 3 1 l η).trans ((hi 2 1 (outgoingIndex l) η).trans
      (hp 2 0 (incomingIndex (outgoingIndex l)) η))
  · refine ⟨true,incomingIndex (pairsIndex l),fun η=>?_⟩
    exact (hp 3 2 l η).trans (hi 1 0 (pairsIndex l) η)
  · exact (hij rfl).elim

def markedOmega (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ) : ℝ:=
  ∑l:Fin 4, (markedCost R θ true l η+markedCost R θ false l η)

theorem markedOmega_nonnegative (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ) :
    0 ≤ markedOmega R θ η :=
  Finset.sum_nonneg (fun _ _=>add_nonneg (markedCost_nonnegative _ _ _ _ _)
    (markedCost_nonnegative _ _ _ _ _))

theorem markedCost_le_omega (R : ℝ) (θ : Thermodynamics.Parameter)
    (b : Bool) (l : Fin 4) (η : ℝ) : markedCost R θ b l η ≤ markedOmega R θ η := by
  have hs:=Finset.single_le_sum
    (fun l (_:l∈(Finset.univ:Finset (Fin 4)))=>
      add_nonneg (markedCost_nonnegative R θ true l η) (markedCost_nonnegative R θ false l η))
    (Finset.mem_univ l)
  cases b
  · exact (le_add_of_nonneg_left (markedCost_nonnegative R θ true l η)).trans hs
  · exact (le_add_of_nonneg_right (markedCost_nonnegative R θ false l η)).trans hs

theorem markedOmega_tendsto {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    Tendsto (markedOmega R θ) (𝓝 0) (𝓝 0) := by
  have h:=tendsto_finset_sum (Finset.univ:Finset (Fin 4)) (fun l _=>
    (actual_marked_cost_tendsto hR hθ true l).add (actual_marked_cost_tendsto hR hθ false l))
  simpa only [add_zero,Finset.sum_const_zero,markedOmega] using h

theorem all_marked_norm_bound {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i j l : Fin 4) (hij : i≠j) (η : ℝ) :
    ‖markedOperator R θ i j l η‖ ≤ markedOmega R θ η := by
  obtain ⟨b,l',he⟩:=actual_all_marked_choice R θ i j l hij
  rw [he η]
  exact (actual_marked_norm_bound hR hθ b l' η).trans (markedCost_le_omega R θ b l' η)

/-- This is one original quartet integral, with all observed and marked
addresses transformed together, and no independent marginal replacement. -/
theorem actual_full_marked_pair_bound {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i j l : Fin 4) (hij : i≠j)
    (η : ℝ) (u v : H R θ) :
    |∫q,cut R η (q l)*u (q j)*v (q i)∂jointMeasure R θ|
      ≤ markedOmega R θ η*‖u‖*‖v‖ := by
  rw [←actual_marked_pairing]
  calc
    _ ≤ ‖v‖*‖markedOperator R θ i j l η u‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(‖markedOperator R θ i j l η‖*‖u‖) :=
      mul_le_mul_of_nonneg_left ((markedOperator R θ i j l η).le_opNorm u) (norm_nonneg _)
    _ ≤ ‖v‖*(markedOmega R θ η*‖u‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (all_marked_norm_bound hR hθ i j l hij η) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

end
end Resonance.AllMarkedQuartetReaders
