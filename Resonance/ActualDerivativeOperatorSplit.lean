import Resonance.ActualStrongDerivativeForm
import Resonance.FullLocalizedDerivativeSplit

/-! The complete actual derivative reader is split only after all sixteen
parents are formed. Its four diagonal readers are symmetric and converge
strongly; all twelve remaining readers converge in operator norm. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.ActualDerivativeOperatorSplit
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm JointWeightComparison
open FreeTransport FiberContinuity ContinuousCollisionPerturbation
open ActualLocalizedOffDiagonal LocalizedDerivativeCoefficients ActualDerivativeStrong
open QuartetCoefficientLocalization FullLocalizedDerivativeSplit
set_option maxHeartbeats 2600000

def diagonalReader {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) :
    H R unitParameter →L[ℝ] H R unitParameter :=
  ∑i:Fin 4,actualPair hR f N hm hM hf hN i i

def offReader {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) :
    H R unitParameter →L[ℝ] H R unitParameter :=
  ∑i:Fin 4,∑j:Fin 4,if i=j then 0 else actualPair hR f N hm hM hf hN i j

theorem complete_operator_split {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) :
    fullReader hR f N hm hM hf hN=
      diagonalReader hR f N hm hM hf hN+offReader hR f N hm hM hf hN := by
  change (∑i:Fin 4,∑j:Fin 4,actualPair hR f N hm hM hf hN i j)=_
  rw [diagonalReader,offReader,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd : actualPair hR f N hm hM hf hN i i=
      ∑j:Fin 4,if i=j then actualPair hR f N hm hM hf hN i j else 0 := by simp
  rw [hd,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij:i=j <;> simp only [hij,if_true,if_false,add_zero,zero_add]

theorem pair_diagonal_symmetric {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M)
    (i : Fin 4) (u v : H R unitParameter) :
    inner ℝ (actualPair hR f N hm hM hf hN i i u) v=
      inner ℝ u (actualPair hR f N hm hM hf hN i i v) := by
  rw [real_inner_comm]
  simp only [actualPair,pairReader_pairing]
  apply integral_congr_ae
  exact ae_of_all _ (fun _=>by ring)

theorem diagonal_symmetric {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M)
    (u v : H R unitParameter) :
    inner ℝ (diagonalReader hR f N hm hM hf hN u) v=
      inner ℝ u (diagonalReader hR f N hm hM hf hN v) := by
  simp only [diagonalReader,ContinuousLinearMap.sum_apply,sum_inner,inner_sum]
  exact Finset.sum_congr rfl (fun i _=>pair_diagonal_symmetric hR f N hm hM hf hN i u v)

theorem actual_pair_off_norm {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M κ η : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hκ : 0 ≤ κ)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M)
    (hbulk : ∀k:MomentumDomain R,η < CornerFrequencyBounds.cornerDepth R k → |f k-N k| ≤ κ)
    (i j : Fin 4) (hij : i≠j) :
    ‖actualPair hR f N hm hM hf hN i j‖ ≤ energyCost R m M κ η := by
  let T:=actualPair hR f N hm hM hf hN i j
  have hC:=energyCost_nonnegative R η hm hM hκ
  apply ContinuousLinearMap.opNorm_le_bound T hC
  intro u
  have he:=actual_coefficient_envelope hR f N hm hM hκ hf hN hbulk i j
  have hb:=(actual_signed_coefficient_bound hR (unitParameter_positive R) j i hij.symm
    (show 0 ≤ (6*M^2/m)*κ by positivity) (show 0 ≤ 12*M^3/m by positivity)
    η u (T u) (coefficientAt_measurable R f N i j).aestronglyMeasurable he).2
  rw [←pairReader_pairing] at hb
  change |inner ℝ (T u) (T u)| ≤ energyCost R m M κ η*‖u‖*‖T u‖ at hb
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hb
  by_cases ht:T u=0
  · simp [ht,mul_nonneg hC (norm_nonneg u)]
  · exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr ht)).mp (by nlinarith [hb])

theorem actual_off_norm {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M κ η : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hκ : 0 ≤ κ)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M)
    (hbulk : ∀k:MomentumDomain R,η < CornerFrequencyBounds.cornerDepth R k → |f k-N k| ≤ κ) :
    ‖offReader hR f N hm hM hf hN‖ ≤ 16*energyCost R m M κ η := by
  have hC:=energyCost_nonnegative R η hm hM hκ
  calc
    _ ≤ ∑i:Fin 4,‖∑j:Fin 4,if i=j then (0:H R unitParameter →L[ℝ] H R unitParameter)
        else actualPair hR f N hm hM hf hN i j‖ := norm_sum_le _ _
    _ ≤ ∑i:Fin 4,∑j:Fin 4,‖if i=j then (0:H R unitParameter →L[ℝ] H R unitParameter)
        else actualPair hR f N hm hM hf hN i j‖ :=
      Finset.sum_le_sum (fun i _=>norm_sum_le _ _)
    _ ≤ ∑_i:Fin 4,∑_j:Fin 4,energyCost R m M κ η := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij:i=j
      · simpa only [if_pos hij,norm_zero] using hC
      · simpa only [if_neg hij] using actual_pair_off_norm hR f N hm hM hκ hf hN hbulk i j hij
    _ = _ := by simp; ring

theorem actual_off_family_norm_tendsto {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f N : I→CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀s k,m ≤ N s k ∧ |N s k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N s k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun s=>‖offReader hR (f s) (N s) hm hM (hf s) (hN s)‖) l (𝓝 0) := by
  have hp : Tendsto (fun s=>(|κ s|,η s)) l (𝓝 ((0,0):ℝ×ℝ)) := by
    simpa only [abs_zero] using hκ.abs.prodMk_nhds hη
  have ht:=((actual_offdiagonal_cost_tendsto hR m M).comp hp).const_mul 16
  simp only [mul_zero] at ht
  exact squeeze_zero (fun _=>norm_nonneg _)
    (fun s=>actual_off_norm hR (f s) (N s) hm hM (abs_nonneg _) (hf s) (hN s) (hbulk s)) ht

theorem actual_diagonal_family_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f N : I→CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀s k,m ≤ N s k ∧ |N s k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N s k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (u : H R unitParameter) :
    Tendsto (fun s=>diagonalReader hR (f s) (N s) hm hM (hf s) (hN s) u) l (𝓝 0) := by
  have hh:=tendsto_finset_sum (Finset.univ:Finset (Fin 4)) (fun i _=>
    actual_pair_family_strong hR l f N hm hM hf hN κ η hbulk hκ hη i i u)
  simpa only [diagonalReader,Finset.sum_const_zero,ContinuousLinearMap.sum_apply] using hh

end
end Resonance.ActualDerivativeOperatorSplit
