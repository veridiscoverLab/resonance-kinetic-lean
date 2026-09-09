import Resonance.EffectiveGradientSpace
import Resonance.DeviatoricRankOne

/-! Exact Frobenius geometry of the eight effective gradient coordinates. -/
open scoped BigOperators
namespace Resonance.EffectiveGradientNorm
noncomputable section
open EffectiveGradientSpace DeviatoricRankOne
set_option maxHeartbeats 800000

def effectiveEnergy (p : Fin 8→ℝ) : ℝ :=
  p 0^2+p 1^2+p 2^2+(2/3 : ℝ)*(p 3^2+p 3*p 4+p 4^2)+
    (1/2 : ℝ)*(p 5^2+p 6^2+p 7^2)

theorem original_gradient_energy (a h : Fin 3→ℝ) (B : Fin 3→Fin 3→ℝ) :
    effectiveEnergy (observation (OnsagerGradientPolynomial.gradient a B h))=
      frobeniusSq (deviatoric B)+normSq h := by
  simp [effectiveEnergy,observation,OnsagerGradientPolynomial.gradient,
    frobeniusSq,deviatoric,traceThree,normSq,Fin.sum_univ_succ]
  ring

theorem effective_energy_square_bounds (p : Fin 8→ℝ) :
    (∑i,p i^2)/3 ≤ effectiveEnergy p ∧ effectiveEnergy p ≤ ∑i,p i^2 := by
  simp [effectiveEnergy,Fin.sum_univ_succ]
  constructor <;> nlinarith [sq_nonneg (p 0),sq_nonneg (p 1),sq_nonneg (p 2),
    sq_nonneg (p 3+p 4),sq_nonneg (p 3-p 4),sq_nonneg (p 5),
    sq_nonneg (p 6),sq_nonneg (p 7)]

theorem norm_square_le_sum (p : Fin 8→ℝ) : ‖p‖^2 ≤ ∑i,p i^2 := by
  have hs : 0 ≤ ∑i,p i^2 := Finset.sum_nonneg fun i _=>sq_nonneg _
  have hsq := Real.sq_sqrt hs
  have hn : ‖p‖ ≤ Real.sqrt (∑i,p i^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : p i^2 ≤ ∑j,p j^2 := Finset.single_le_sum
      (fun j _=>sq_nonneg (p j)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (p i),sq_abs (p i),Real.sqrt_nonneg (∑j,p j^2)]
  nlinarith [norm_nonneg p,Real.sqrt_nonneg (∑i,p i^2)]

theorem sum_square_le_norm (p : Fin 8→ℝ) : (∑i,p i^2) ≤ 8*‖p‖^2 := by
  have hi : ∀i,p i^2 ≤ ‖p‖^2 := by
    intro i
    have hh := norm_le_pi_norm p i
    rw [Real.norm_eq_abs] at hh
    nlinarith [abs_nonneg (p i),sq_abs (p i)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _=>hi i)
  simpa using hh

theorem effective_energy_norm_bounds (p : Fin 8→ℝ) :
    ‖p‖^2 ≤ 3*effectiveEnergy p ∧ effectiveEnergy p ≤ 8*‖p‖^2 := by
  have he := effective_energy_square_bounds p
  have hl := norm_square_le_sum p
  have hu := sum_square_le_norm p
  constructor <;> linarith

end
end Resonance.EffectiveGradientNorm
