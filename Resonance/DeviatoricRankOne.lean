import Resonance.RankOneGradient

/-! An explicit rank-one identity for the paper's Frobenius deviatoric norm.
It retains all three coordinates and supplies the directional constants. -/
open scoped BigOperators
namespace Resonance.DeviatoricRankOne
noncomputable section

def normSq (v : Fin 3→ℝ) : ℝ := ∑i,v i^2

def traceThree (B : Fin 3→Fin 3→ℝ) : ℝ := ∑i,B i i

def deviatoric (B : Fin 3→Fin 3→ℝ) (i j : Fin 3) : ℝ :=
  (B i j+B j i)/2-if i=j then traceThree B/3 else 0

def frobeniusSq (B : Fin 3→Fin 3→ℝ) : ℝ := ∑i,∑j,B i j^2

theorem rank_one_identity (ell b : Fin 3→ℝ) :
    frobeniusSq (deviatoric (fun i j=>ell i*b j))=
      normSq ell*normSq b/2+(∑i,ell i*b i)^2/6 := by
  simp [frobeniusSq,deviatoric,traceThree,normSq,Fin.sum_univ_succ]
  ring

theorem rank_one_lower (ell b : Fin 3→ℝ) :
    normSq ell*normSq b/2≤frobeniusSq (deviatoric (fun i j=>ell i*b j)) := by
  rw [rank_one_identity]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by norm_num))

theorem dot_square_bound (ell b : Fin 3→ℝ) :
    (∑i,ell i*b i)^2≤normSq ell*normSq b := by
  have h01 := sq_nonneg (ell 0*b 1-ell 1*b 0)
  have h02 := sq_nonneg (ell 0*b 2-ell 2*b 0)
  have h12 := sq_nonneg (ell 1*b 2-ell 2*b 1)
  simp [normSq,Fin.sum_univ_succ]
  nlinarith

theorem rank_one_upper (ell b : Fin 3→ℝ) :
    frobeniusSq (deviatoric (fun i j=>ell i*b j))≤(2/3 : ℝ)*normSq ell*normSq b := by
  rw [rank_one_identity]
  have hh := dot_square_bound ell b
  linarith

theorem rank_one_energy_norm (ell : Fin 3→ℝ) (e : ℝ) :
    normSq (fun j=>ell j*e)=normSq ell*e^2 := by
  simp only [normSq,mul_pow,Finset.sum_mul]

end
end Resonance.DeviatoricRankOne
