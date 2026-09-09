import Resonance.ActualFourierRank

/-! Literal complex matrices and their real/imaginary quadratic decomposition. -/
open scoped BigOperators ComplexConjugate
namespace Resonance.RealMatrixComplexification
noncomputable section

def complexify {I : Type*} (M : Matrix I I ℝ) : Matrix I I ℂ := fun i j=>(M i j : ℂ)

theorem mulVec_re {I : Type*} [Fintype I] (M : Matrix I I ℝ) (z : I→ℂ) (i : I) :
    ((complexify M).mulVec z i).re=M.mulVec (fun j=>(z j).re) i := by
  simp [complexify,Matrix.mulVec,dotProduct,Complex.mul_re]

theorem mulVec_im {I : Type*} [Fintype I] (M : Matrix I I ℝ) (z : I→ℂ) (i : I) :
    ((complexify M).mulVec z i).im=M.mulVec (fun j=>(z j).im) i := by
  simp [complexify,Matrix.mulVec,dotProduct,Complex.mul_im]

theorem complex_kernel_iff {I : Type*} [Fintype I] (M : Matrix I I ℝ) (z : I→ℂ) :
    (complexify M).mulVec z=0 ↔
      M.mulVec (fun j=>(z j).re)=0 ∧ M.mulVec (fun j=>(z j).im)=0 := by
  constructor
  · intro h
    constructor
    · funext i
      rw [←mulVec_re,h]
      rfl
    · funext i
      rw [←mulVec_im,h]
      rfl
  · rintro ⟨hr,hi⟩
    funext i
    apply Complex.ext
    · rw [mulVec_re,hr]
      rfl
    · rw [mulVec_im,hi]
      rfl

theorem quadratic_re {I : Type*} [Fintype I] (M : Matrix I I ℝ) (z : I→ℂ) :
    (∑i,conj (z i)*((complexify M).mulVec z i)).re=
      (∑i,(z i).re*(M.mulVec (fun j=>(z j).re) i))+
      (∑i,(z i).im*(M.mulVec (fun j=>(z j).im) i)) := by
  simp only [Complex.re_sum,Complex.mul_re,Complex.conj_re,Complex.conj_im,mulVec_re,mulVec_im]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem real_bilinear_symmetric {I : Type*} [Fintype I] (M : Matrix I I ℝ)
    (hs : ∀i j,M i j=M j i) (x y : I→ℝ) :
    (∑i,x i*(M.mulVec y i))=∑i,y i*(M.mulVec x i) := by
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring

theorem quadratic_im_zero {I : Type*} [Fintype I] (M : Matrix I I ℝ)
    (hs : ∀i j,M i j=M j i) (z : I→ℂ) :
    (∑i,conj (z i)*((complexify M).mulVec z i)).im=0 := by
  simp only [Complex.im_sum,Complex.mul_im,Complex.conj_re,Complex.conj_im,mulVec_re,mulVec_im]
  simp only [neg_mul,←sub_eq_add_neg,Finset.sum_sub_distrib]
  rw [real_bilinear_symmetric M hs,sub_self]

end
end Resonance.RealMatrixComplexification
