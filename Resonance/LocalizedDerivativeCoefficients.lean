import Resonance.QuartetDerivativeBounds
import Resonance.QuartetCoefficientLocalization

/-! Full original cubic derivative coefficients with a displayed
bulk/corner envelope. Diagonal and off-diagonal terms are separated only
after the complete four-parent difference has been formed. -/
open Set MeasureTheory
namespace Resonance.LocalizedDerivativeCoefficients
noncomputable section
open Collision CollisionLinearization QuartetDerivativeBounds
open ResonantMeasure CornerPairTruncation QuartetCoefficientLocalization
set_option maxHeartbeats 1800000

def testSign (j : Fin 4) : ℝ:=![1,1,-1,-1] j

theorem testSign_abs (j : Fin 4) : |testSign j|=1 := by fin_cases j <;> norm_num [testSign]

theorem delta_testSign (v : Quartet) : delta v=∑j:Fin 4,testSign j*v j := by
  simp [delta,testSign,Fin.sum_univ_succ]
  ring

def relativeCoefficient (f N : Quartet) (i j : Fin 4) : ℝ:=
  (1/4:ℝ)*(coefficient f i-coefficient N i)*(N i/N j)*testSign j

theorem complete_parent_pair_identity (f N u : Quartet) :
    (1/4:ℝ)*(linearCoefficient f (fun i=>N i*u i)-linearCoefficient N (fun i=>N i*u i))*
      delta (fun j=>u j/N j)=
        ∑i:Fin 4,∑j:Fin 4,relativeCoefficient f N i j*u i*u j := by
  rw [full_derivative_coefficient,full_derivative_coefficient,delta_testSign]
  simp only [relativeCoefficient,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,div_eq_mul_inv]
  ring

def diagonalPart (f N u : Quartet) : ℝ:=∑i:Fin 4,relativeCoefficient f N i i*(u i)^2

def offDiagonalPart (f N u : Quartet) : ℝ:=
  ∑i:Fin 4,∑j:Fin 4,if i=j then 0 else relativeCoefficient f N i j*u i*u j

theorem complete_diagonal_offdiagonal_identity (f N u : Quartet) :
    (1/4:ℝ)*(linearCoefficient f (fun i=>N i*u i)-linearCoefficient N (fun i=>N i*u i))*
      delta (fun j=>u j/N j)=diagonalPart f N u+offDiagonalPart f N u := by
  rw [complete_parent_pair_identity]
  simp [diagonalPart,offDiagonalPart,Fin.sum_univ_succ]
  ring

theorem relativeCoefficient_bound (f N : Quartet) {m M δ : ℝ}
    (hm : 0 < m) (hM : 0≤M) (hδ : 0≤δ) (hf : ∀i,|f i|≤M)
    (hN : ∀i,m≤N i ∧ |N i|≤M) (hd : ∀i,|f i-N i|≤δ) (i j : Fin 4) :
    |relativeCoefficient f N i j|≤(6*M^2/m)*δ := by
  have hc:=coefficient_difference_bound f N hM hδ hf (fun i=>(hN i).2) hd i
  have hn : |N i/N j|≤M/m := by
    rw [abs_div,abs_of_pos (hm.trans_le (hN j).1)]
    exact div_le_div₀ hM (hN i).2 hm (hN j).1
  rw [relativeCoefficient,abs_mul,abs_mul,abs_mul,testSign_abs,mul_one,
    abs_of_nonneg (by norm_num:(0:ℝ)≤1/4)]
  calc
    _ ≤ ((1/4:ℝ)*(6*M*δ))*(M/m) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hn
        (abs_nonneg _) (by positivity)
    _ ≤ (6*M*δ)*(M/m) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6) hM) hδ]) (by positivity)
    _ = _ := by ring

theorem coefficient_measurable {A : Type*} [MeasurableSpace A] (f : A→Quartet)
    (hf : ∀i,Measurable (fun x=>f x i)) (i : Fin 4) : Measurable (fun x=>coefficient (f x) i) := by
  unfold coefficient
  exact Finset.measurable_sum _ (fun j _=>measurable_const.mul ((hf _).mul (hf _)))

theorem relativeCoefficient_measurable {A : Type*} [MeasurableSpace A] (f N : A→Quartet)
    (hf : ∀i,Measurable (fun x=>f x i)) (hN : ∀i,Measurable (fun x=>N x i))
    (i j : Fin 4) : Measurable (fun x=>relativeCoefficient (f x) (N x) i j) := by
  exact ((measurable_const.mul ((coefficient_measurable f hf i).sub
    (coefficient_measurable N hN i))).mul ((hN i).div (hN j))).mul measurable_const

/-- This retains each actual mark, including free coefficient legs. -/
theorem relativeCoefficient_marked_bound (f N : Quartet) (χ : Fin 4→ℝ) {m M κ : ℝ}
    (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ) (hχ : ∀i,0≤χ i)
    (hf : ∀i,|f i|≤M) (hN : ∀i,m≤N i ∧ |N i|≤M)
    (hd : ∀i,|f i-N i|≤κ+2*M*χ i) (i j : Fin 4) :
    |relativeCoefficient f N i j|≤(6*M^2/m)*κ+(12*M^3/m)*(∑l,χ l) := by
  have hs:∀i,χ i≤∑l,χ l:=fun i=>Finset.single_le_sum (fun l _=>hχ l) (Finset.mem_univ i)
  have hS : 0≤∑l,χ l:=Finset.sum_nonneg (fun l _=>hχ l)
  have h2M : 0≤2*M:=mul_nonneg (by norm_num) hM
  have hδ : 0≤κ+2*M*(∑l,χ l):=add_nonneg hκ (mul_nonneg h2M hS)
  have hd' : ∀i,|f i-N i|≤κ+2*M*(∑l,χ l) := by
    intro i
    have hmono:2*M*χ i≤2*M*(∑l,χ l):=mul_le_mul_of_nonneg_left (hs i) h2M
    exact (hd i).trans (by linarith)
  have hb:=relativeCoefficient_bound f N hm hM hδ hf hN hd' i j
  exact hb.trans_eq (by ring)

end
end Resonance.LocalizedDerivativeCoefficients
