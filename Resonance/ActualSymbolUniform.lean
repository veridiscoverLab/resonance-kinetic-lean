import Resonance.ActualOnsagerUniform
import Resonance.ActualComplexSymbol

/-! Uniform real and complex bounds for the original contracted Fourier
symbol, with its mass direction retained and the other four components. -/
open Set
open scoped BigOperators ComplexConjugate
namespace Resonance.ActualSymbolUniform
noncomputable section
set_option maxHeartbeats 800000
open Thermodynamics ActualFourierSymbol ActualComplexSymbol ActualOnsagerUniform
open ActualOnsagerPositive RankOneGradient DeviatoricRankOne RealMatrixComplexification

def tailSquare (e : Fin 5→ℝ) : ℝ := ∑i : Fin 4,e i.succ^2

theorem tail_square_identity (e : Fin 5→ℝ) :
    tailSquare e=normSq (fun i : Fin 3=>e i.castSucc.succ)+e 4^2 := by
  simp [tailSquare,normSq,Fin.sum_univ_succ]
  ring

theorem original_real_symbol_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K ⊆ positiveDomain R) :
    ∃a A : ℝ,0 < a ∧ 0 < A ∧ ∀θ : K,∀ell : Fin 3→ℝ,∀e : Fin 5→ℝ,
      a*normSq ell*tailSquare e ≤ ∑i,e i*((symbol hR (hpos θ.property) ell).mulVec e i) ∧
      (∑i,e i*((symbol hR (hpos θ.property) ell).mulVec e i)) ≤ A*normSq ell*tailSquare e := by
  obtain ⟨a,A,ha,hA,hb⟩ := original_deviatoric_bounds hR hK hpos
  refine ⟨a/2,A,by positivity,hA,?_⟩
  intro θ ell e
  rw [symbol_quadratic_identity,rankOne_as_gradient,tail_square_identity]
  have hh := hb θ (fun j=>ell j*e 0) (fun j=>ell j*e 4)
    (fun j l=>ell j*e l.castSucc.succ)
  rw [rank_one_energy_norm] at hh
  have hl := rank_one_lower ell (fun i : Fin 3=>e i.castSucc.succ)
  have hu := rank_one_upper ell (fun i : Fin 3=>e i.castSucc.succ)
  have hnell : 0 ≤ normSq ell := Finset.sum_nonneg fun i _=>sq_nonneg _
  have hnb : 0 ≤ normSq (fun i : Fin 3=>e i.castSucc.succ) :=
    Finset.sum_nonneg fun i _=>sq_nonneg _
  constructor
  · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hl),
      mul_nonneg ha.le (mul_nonneg hnell (sq_nonneg (e 4)))]
  · nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hu),
      mul_nonneg hA.le (mul_nonneg hnell hnb)]

def complexTailSquare (z : Fin 5→ℂ) : ℝ :=
  tailSquare (fun i=>(z i).re)+tailSquare (fun i=>(z i).im)

theorem original_complex_symbol_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K ⊆ positiveDomain R) :
    ∃a A : ℝ,0 < a ∧ 0 < A ∧ ∀θ : K,∀ell : Fin 3→ℝ,∀z : Fin 5→ℂ,
      a*normSq ell*complexTailSquare z ≤
        (∑i,conj (z i)*((complexSymbol hR (hpos θ.property) ell).mulVec z i)).re ∧
      (∑i,conj (z i)*((complexSymbol hR (hpos θ.property) ell).mulVec z i)).re ≤
        A*normSq ell*complexTailSquare z := by
  obtain ⟨a,A,ha,hA,hb⟩ := original_real_symbol_bounds hR hK hpos
  refine ⟨a,A,ha,hA,?_⟩
  intro θ ell z
  have hr := hb θ ell (fun i=>(z i).re)
  have hi := hb θ ell (fun i=>(z i).im)
  simp only [complexSymbol,quadratic_re,complexTailSquare,mul_add]
  exact ⟨add_le_add hr.1 hi.1,add_le_add hr.2 hi.2⟩

theorem original_symbol_entry_continuous {R : ℝ} (hR : 0 < R) (a b : Fin 5) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>symbol hR p.1.property p.2 a b) := by
  simp_rw [symbol_original_contraction]
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  exact (((continuous_apply i).comp continuous_snd).mul
    ((ActualOnsagerContinuity.actual_tensor_entry_continuous hR (i,a) (j,b)).comp
      continuous_fst)).mul ((continuous_apply j).comp continuous_snd)

theorem original_symbol_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>symbol hR p.1.property p.2) :=
  continuous_pi (fun i=>continuous_pi (fun j=>original_symbol_entry_continuous hR i j))

end
end Resonance.ActualSymbolUniform
