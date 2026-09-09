import Resonance.FrequencyWeightedKernel

/-! Exact diagonal and off-diagonal structure of the same complete Gram
operator.  Simultaneous quartet symmetries identify its cross terms; no
compactness or positive gap is asserted by this algebraic decomposition. -/
open MeasureTheory
namespace Resonance.FrequencyGramDecomposition
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm

def cross (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4) : H R θ→L[ℝ]H R θ :=
  (pullback R θ i).toContinuousLinearMap.adjoint.comp
    (pullback R θ j).toContinuousLinearMap

theorem cross_pairing (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4)
    (f g : H R θ) : inner ℝ f (cross R θ i j g)=
      inner ℝ (pullback R θ i f) (pullback R θ j g) :=
  ContinuousLinearMap.adjoint_inner_right (pullback R θ i).toContinuousLinearMap
    f (pullback R θ j g)

theorem cross_diagonal (R : ℝ) (θ : Thermodynamics.Parameter) (i : Fin 4) :
    cross R θ i i=1 := (pullback R θ i).adjoint_comp_self

theorem pullback_relabel (R : ℝ) (θ : Thermodynamics.Parameter)
    (S : FourMomenta→FourMomenta)
    (hS : MeasurePreserving S (jointMeasure R θ) (jointMeasure R θ))
    {i j : Fin 4} (hij : ∀q,S q i=q j) (f : H R θ) :
    Lp.compMeasurePreservingₗᵢ ℝ S hS (pullback R θ i f)=pullback R θ j f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (pullback R θ i f) hS,
    hS.quasiMeasurePreserving.ae_eq (pullback_ae R θ i f),pullback_ae R θ j f]
    with q hs hi hj
  simp only [Function.comp_def,hij] at hi
  exact hs.trans (hi.trans hj.symm)

theorem cross_relabel (R : ℝ) (θ : Thermodynamics.Parameter)
    (S : FourMomenta→FourMomenta)
    (hS : MeasurePreserving S (jointMeasure R θ) (jointMeasure R θ))
    {i j i' j' : Fin 4} (hi : ∀q,S q i=q i') (hj : ∀q,S q j=q j') :
    cross R θ i j=cross R θ i' j' := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro f
  rw [cross_pairing,cross_pairing,
    ←pullback_relabel R θ S hS hi f,←pullback_relabel R θ S hS hj g]
  exact (Lp.compMeasurePreservingₗᵢ ℝ S hS : J R θ→ₗᵢ[ℝ]J R θ).inner_map_map _ _ |>.symm

theorem cross_incoming (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4) :
    cross R θ i j=cross R θ (![1,0,2,3] i) (![1,0,2,3] j) :=
  cross_relabel R θ swapIncomingK (incoming_preserves_joint R θ)
    (fun _=>by fin_cases i <;> rfl) (fun _=>by fin_cases j <;> rfl)

theorem cross_outgoing (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4) :
    cross R θ i j=cross R θ (![0,1,3,2] i) (![0,1,3,2] j) :=
  cross_relabel R θ swapOutgoingK (outgoing_preserves_joint R θ)
    (fun _=>by fin_cases i <;> rfl) (fun _=>by fin_cases j <;> rfl)

theorem cross_pairs (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4) :
    cross R θ i j=cross R θ (![2,3,0,1] i) (![2,3,0,1] j) :=
  cross_relabel R θ swapPairsK (pairs_preserves_joint R θ)
    (fun _=>by fin_cases i <;> rfl) (fun _=>by fin_cases j <;> rfl)

theorem cross_relations (R : ℝ) (θ : Thermodynamics.Parameter) :
    cross R θ 1 0=cross R θ 0 1 ∧ cross R θ 2 3=cross R θ 0 1 ∧
    cross R θ 3 2=cross R θ 0 1 ∧ cross R θ 0 3=cross R θ 0 2 ∧
    cross R θ 1 2=cross R θ 0 2 ∧ cross R θ 1 3=cross R θ 0 2 ∧
    cross R θ 2 0=cross R θ 0 2 ∧ cross R θ 2 1=cross R θ 0 2 ∧
    cross R θ 3 0=cross R θ 0 2 ∧ cross R θ 3 1=cross R θ 0 2 := by
  have h10 : cross R θ 1 0=cross R θ 0 1 := by simpa using cross_incoming R θ 1 0
  have h23 : cross R θ 2 3=cross R θ 0 1 := by simpa using cross_pairs R θ 2 3
  have h32 : cross R θ 3 2=cross R θ 0 1 := by
    simpa [h10] using cross_pairs R θ 3 2
  have h03 : cross R θ 0 3=cross R θ 0 2 := by simpa using cross_outgoing R θ 0 3
  have h12 : cross R θ 1 2=cross R θ 0 2 := by simpa using cross_incoming R θ 1 2
  have h13 : cross R θ 1 3=cross R θ 0 2 := by
    simpa [h03] using cross_incoming R θ 1 3
  have h20 : cross R θ 2 0=cross R θ 0 2 := by simpa using cross_pairs R θ 2 0
  have h21 : cross R θ 2 1=cross R θ 0 2 := by
    simpa [h20] using cross_incoming R θ 2 1
  have h30 : cross R θ 3 0=cross R θ 0 2 := by
    simpa [h20] using cross_outgoing R θ 3 0
  have h31 : cross R θ 3 1=cross R θ 0 2 := by
    simpa [h30] using cross_incoming R θ 3 1
  exact ⟨h10,h23,h32,h03,h12,h13,h20,h21,h30,h31⟩

/-- All diagonal legs give the identity, and the common full-quartet
symmetries leave precisely the two original cross operators. -/
theorem gram_eq_identity_add_cross (R : ℝ) (θ : Thermodynamics.Parameter) :
    gram R θ=1+cross R θ 0 1-(2 : ℝ) • cross R θ 0 2 := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro f
  obtain ⟨h10,h23,h32,h03,h12,h13,h20,h21,h30,h31⟩ := cross_relations R θ
  rw [gram_pairing]
  simp only [fullDifference,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    real_inner_smul_left,inner_add_left,inner_sub_left,
    real_inner_smul_right,inner_add_right,inner_sub_right]
  simp_rw [←cross_pairing]
  simp only [cross_diagonal,h10,h23,h32,h03,h12,h13,h20,h21,h30,h31]
  norm_num
  ring

end
end Resonance.FrequencyGramDecomposition
