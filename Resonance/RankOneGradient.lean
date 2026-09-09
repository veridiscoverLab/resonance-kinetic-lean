import Resonance.ActualOnsagerNullDirections

/-! The exact three-dimensional rank-one consequence of the original
Onsager null condition. No choice of a preferred frequency direction is made. -/
namespace Resonance.RankOneGradient
noncomputable section
open ActualOnsagerTensor OnsagerGradientPolynomial

theorem nonzero_coordinate {ell : Fin 3→ℝ} (hell : ell≠0) : ∃i,ell i≠0 := by
  by_contra hn
  push Not at hn
  exact hell (funext hn)

theorem scalar_symmetric_rank_one {ell b : Fin 3→ℝ} {c : ℝ} (hell : ell≠0)
    (hs : ∀i j,ell i*b j+ell j*b i=if i=j then 2*c else 0) : b=0 ∧ c=0 := by
  obtain ⟨i,hi⟩ := nonzero_coordinate hell
  obtain ⟨j,hji⟩ := exists_ne i
  have hii : ell i*b i=c := by
    have hh := hs i i
    simp only [ite_true] at hh
    linarith
  have hjj : ell j*b j=c := by
    have hh := hs j j
    simp only [ite_true] at hh
    linarith
  have hij : ell i*b j+ell j*b i=0 := by simpa only [if_neg hji.symm] using hs i j
  have he : (ell i^2+ell j^2)*b i=0 := by
    linear_combination ell j*hij-ell i*hjj+ell i*hii
  have hp : 0<ell i^2+ell j^2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hi) (sq_nonneg _)
  have hbi : b i=0 := (mul_eq_zero.mp he).resolve_left hp.ne'
  have hc : c=0 := by simpa only [hbi,mul_zero] using hii.symm
  refine ⟨?_,hc⟩
  funext k
  have hk := hs i k
  simp only [hbi,mul_zero,add_zero,hc,mul_zero,ite_self] at hk
  exact (mul_eq_zero.mp hk).resolve_left hi

def rankOne (ell : Fin 3→ℝ) (e : Fin 5→ℝ) : Index→ℝ := fun i=>ell i.1*e i.2

theorem rankOne_as_gradient (ell : Fin 3→ℝ) (e : Fin 5→ℝ) :
    rankOne ell e=gradient (fun j=>ell j*e 0)
      (fun j l=>ell j*e l.castSucc.succ) (fun j=>ell j*e 4) := by
  funext i
  rcases i with ⟨j,l⟩
  fin_cases l <;> rfl

theorem rankOne_null_iff {ell : Fin 3→ℝ} (hell : ell≠0) (e : Fin 5→ℝ) :
    OnsagerPolynomial.nullDirections (fun j=>ell j*e 4) (fun j l=>ell j*e l.castSucc.succ)
      ↔ e 1=0 ∧ e 2=0 ∧ e 3=0 ∧ e 4=0 := by
  rw [OnsagerPolynomial.nullDirections_iff_scalar_symmetric]
  constructor
  · rintro ⟨hh,c,hc⟩
    obtain ⟨i,hi⟩ := nonzero_coordinate hell
    have h4 := (mul_eq_zero.mp (hh i)).resolve_left hi
    have hb := (scalar_symmetric_rank_one hell hc).1
    exact ⟨congrFun hb 0,congrFun hb 1,congrFun hb 2,h4⟩
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨fun j=>by rw [h4,mul_zero],0,?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h1,h2,h3]

end
end Resonance.RankOneGradient
