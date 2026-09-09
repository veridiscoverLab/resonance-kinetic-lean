import Resonance.ContinuousWeightedEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Quantitative bounds for the complete original cubic derivative. The
address and sign table is proved equal to DCpoly, and is used to control
the actual same-quartet energy perturbation rather than independent legs. -/
open Set MeasureTheory
namespace Resonance.QuartetDerivativeBounds
noncomputable section
open Collision CollisionLinearization
set_option maxHeartbeats 1200000

def pairAddresses (i : Fin 4) : Fin 3→Fin 2→Fin 4 :=
  ![![![2,3],![1,3],![1,2]],![![2,3],![0,3],![0,2]],
    ![![1,3],![0,3],![0,1]],![![1,2],![0,2],![0,1]]] i
def parentSign (i : Fin 4) : Fin 3→ℝ := ![![1,-1,-1],![1,-1,-1],![1,1,-1],![1,1,-1]] i
def coefficient (f : Quartet) (i : Fin 4) : ℝ :=
  ∑j:Fin 3,parentSign i j*(f (pairAddresses i j 0)*f (pairAddresses i j 1))

theorem parentSign_abs (i : Fin 4) (j : Fin 3) : |parentSign i j|=1 := by
  fin_cases i <;> fin_cases j <;> norm_num [parentSign]

theorem full_derivative_coefficient (f h : Quartet) :
    linearCoefficient f h=∑i:Fin 4,coefficient f i*h i := by
  simp [linearCoefficient,coefficient,pairAddresses,parentSign,Fin.sum_univ_succ]
  ring

theorem product_difference_bound {a b A B M δ:ℝ} (hM:0≤M) (hδ:0≤δ)
    (hb:|b|≤M) (hA:|A|≤M) (ha:|a-A|≤δ) (hc:|b-B|≤δ) :
    |a*b-A*B|≤2*M*δ := by
  calc
    |a*b-A*B|=|(a-A)*b+A*(b-B)| := by congr 1; ring
    _≤|(a-A)*b|+|A*(b-B)| := abs_add_le _ _
    _=|a-A| * |b| + |A| * |b-B| := by rw [abs_mul,abs_mul]
    _≤δ*M+M*δ := add_le_add (mul_le_mul ha hb (abs_nonneg _) hδ)
      (mul_le_mul hA hc (abs_nonneg _) hM)
    _=2*M*δ := by ring

theorem coefficient_difference_bound (f N : Quartet) {M δ:ℝ} (hM:0≤M) (hδ:0≤δ)
    (hf:∀i,|f i|≤M) (hN:∀i,|N i|≤M) (hd:∀i,|f i-N i|≤δ) (i:Fin 4) :
    |coefficient f i-coefficient N i|≤6*M*δ := by
  rw [coefficient,coefficient,←Finset.sum_sub_distrib]
  calc
    _≤∑j:Fin 3,|parentSign i j*(f (pairAddresses i j 0)*f (pairAddresses i j 1))-
        parentSign i j*(N (pairAddresses i j 0)*N (pairAddresses i j 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑_j:Fin 3,2*M*δ := by
      apply Finset.sum_le_sum
      intro j _
      rw [←mul_sub,abs_mul,parentSign_abs,one_mul]
      exact product_difference_bound hM hδ (hf _) (hN _) (hd _) (hd _)
    _=6*M*δ := by simp; ring

theorem full_derivative_difference_bound (f N h : Quartet) {M δ:ℝ} (hM:0≤M) (hδ:0≤δ)
    (hf:∀i,|f i|≤M) (hN:∀i,|N i|≤M) (hd:∀i,|f i-N i|≤δ) :
    |linearCoefficient f h-linearCoefficient N h|≤(6*M*δ)*(∑i,|h i|) := by
  rw [full_derivative_coefficient,full_derivative_coefficient,←Finset.sum_sub_distrib]
  calc
    _≤∑i:Fin 4,|coefficient f i*h i-coefficient N i*h i| := Finset.abs_sum_le_sum_abs _ _
    _≤∑i:Fin 4,(6*M*δ)*|h i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [←sub_mul,abs_mul]
      exact mul_le_mul_of_nonneg_right (coefficient_difference_bound f N hM hδ hf hN hd i) (abs_nonneg _)
    _=_ := (Finset.mul_sum _ _ _).symm

theorem delta_abs_le (h : Quartet) : |delta h|≤∑i,|h i| := by
  have ha:=abs_sub_le (h 0+h 1-h 2) 0 (h 3)
  have hb:=abs_sub_le (h 0+h 1) 0 (h 2)
  simp only [sub_zero,zero_sub,abs_neg] at ha hb
  have hc:=abs_add_le (h 0) (h 1)
  simp only [delta,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change |h 0+h 1-h 2-h 3|≤|h 0|+(|h 1|+(|h 2|+|h 3|))
  linarith

theorem l1_square_le_four_squares (u : Quartet) : (∑i,|u i|)^2≤4*(∑i,(u i)^2) := by
  have h:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i:Fin 4=>|u i|) (fun _=> (1:ℝ))
  simpa only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,sq_abs,mul_comm] using h

/-- This pointwise bound will be integrated on the original full quartet.
The right hand side remains a sum of the four actual single-leg squares. -/
theorem normalized_energy_perturbation_bound (f N u : Quartet) {m M δ:ℝ}
    (hm : 0 < m) (hM : 0≤M) (hδ : 0≤δ) (hf : ∀i,|f i|≤M)
    (hN:∀i,m≤N i ∧ |N i|≤M) (hd:∀i,|f i-N i|≤δ) :
    |(1/4:ℝ)*(linearCoefficient f (fun i=>N i*u i)-linearCoefficient N (fun i=>N i*u i))*
      delta (fun i=>u i/N i)|≤(6*M^2*δ/m)*(∑i,(u i)^2) := by
  let S:=∑i,|u i|
  have hS:0≤S:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hprod: (∑i,|N i*u i|)≤M*S := by
    unfold S
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hN i).2 (abs_nonneg _)
  have hlin:=full_derivative_difference_bound f N (fun i=>N i*u i) hM hδ hf (fun i=>(hN i).2) hd
  have hlin': |linearCoefficient f (fun i=>N i*u i)-linearCoefficient N (fun i=>N i*u i)|
      ≤(6*M^2*δ)*S := by
    calc
      _≤(6*M*δ)*(∑i,|N i*u i|):=hlin
      _≤(6*M*δ)*(M*S):=mul_le_mul_of_nonneg_left hprod (by positivity)
      _=_:=by ring
  have hdelt: |delta (fun i=>u i/N i)|≤S/m := by
    calc
      _≤∑i,|u i/N i|:=delta_abs_le _
      _≤∑i,|u i|/m:=by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_div,abs_of_pos (lt_of_lt_of_le hm (hN i).1)]
        exact div_le_div_of_nonneg_left (abs_nonneg _) hm (hN i).1
      _=_:=by rw [Finset.sum_div]
  have hs2: S^2≤4*(∑i,(u i)^2):=l1_square_le_four_squares u
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1/4)]
  calc
    _≤((1/4:ℝ)*((6*M^2*δ)*S))*(S/m):=
      mul_le_mul (mul_le_mul_of_nonneg_left hlin' (by norm_num)) hdelt
        (abs_nonneg _) (by positivity)
    _=(6*M^2*δ/(4*m))*S^2:=by ring
    _≤(6*M^2*δ/(4*m))*(4*(∑i,(u i)^2)):=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    _=_:=by ring

end
end Resonance.QuartetDerivativeBounds

#check Resonance.QuartetDerivativeBounds.parentSign_abs
#check Resonance.QuartetDerivativeBounds.full_derivative_coefficient
#check Resonance.QuartetDerivativeBounds.product_difference_bound
#check Resonance.QuartetDerivativeBounds.coefficient_difference_bound
#check Resonance.QuartetDerivativeBounds.full_derivative_difference_bound
#check Resonance.QuartetDerivativeBounds.delta_abs_le
#check Resonance.QuartetDerivativeBounds.l1_square_le_four_squares
#check Resonance.QuartetDerivativeBounds.normalized_energy_perturbation_bound
#print axioms Resonance.QuartetDerivativeBounds.parentSign_abs
#print axioms Resonance.QuartetDerivativeBounds.full_derivative_coefficient
#print axioms Resonance.QuartetDerivativeBounds.product_difference_bound
#print axioms Resonance.QuartetDerivativeBounds.coefficient_difference_bound
#print axioms Resonance.QuartetDerivativeBounds.full_derivative_difference_bound
#print axioms Resonance.QuartetDerivativeBounds.delta_abs_le
#print axioms Resonance.QuartetDerivativeBounds.l1_square_le_four_squares
#print axioms Resonance.QuartetDerivativeBounds.normalized_energy_perturbation_bound
