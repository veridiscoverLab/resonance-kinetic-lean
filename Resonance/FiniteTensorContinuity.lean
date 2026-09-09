import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Strong continuity on a fixed tensor with a finite coordinate domain.
The finite expansion is exact; no operator-norm continuity of the propagator
is assumed. -/
open Function Filter
open scoped Topology
namespace Resonance.FiniteTensorContinuity
noncomputable section
variable {F G T : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace T]
set_option maxHeartbeats 700000

def basisVector (j : Fin 3) : Fin 3 → ℝ := Pi.single j 1

theorem sum_basis (x : Fin 3 → ℝ) : ∑ j : Fin 3,x j • basisVector j=x := by
  ext i
  simp [basisVector,Finset.sum_apply,Pi.single_apply]

theorem tensor_basis_expansion {n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin 3 → ℝ) F)
    (m : Fin n → Fin 3 → ℝ) :
    A m=∑ q : Fin n → Fin 3,(∏ i : Fin n,m i (q i)) • A (fun i => basisVector (q i)) := by
  have hm : m=fun i => ∑ j : Fin 3,m i j • basisVector j := by
    funext i
    exact (sum_basis (m i)).symm
  calc
    A m=A (fun i => ∑ j : Fin 3,m i j • basisVector j) := congrArg A hm
    _=∑ q : Fin n → Fin 3,A (fun i => m i (q i) • basisVector (q i)) :=
      A.toMultilinearMap.map_sum _
    _=_ := by
      apply Finset.sum_congr rfl
      intro q _
      exact A.toMultilinearMap.map_smul_univ _ _

theorem tensor_norm_le_sum_basis {n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin 3 → ℝ) F) :
    ‖A‖≤∑ q : Fin n → Fin 3,‖A (fun i => basisVector (q i))‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro m
  rw [tensor_basis_expansion]
  apply (norm_sum_le _ _).trans
  calc
    ∑ q : Fin n → Fin 3,‖(∏ i : Fin n,m i (q i)) • A (fun i => basisVector (q i))‖
      ≤ ∑ q : Fin n → Fin 3,(∏ i : Fin n,‖m i‖)*‖A (fun i => basisVector (q i))‖ := by
        apply Finset.sum_le_sum
        intro q _
        rw [norm_smul, norm_prod]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (m i) (q i))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem continuous_of_basis {n : ℕ}
    (A : T → ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin 3 → ℝ) F)
    (hA : ∀ q : Fin n → Fin 3,Continuous (fun t => A t (fun i => basisVector (q i)))) :
    Continuous A := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun s => ∑ q : Fin n → Fin 3,
      ‖A s (fun i => basisVector (q i))-A t (fun i => basisVector (q i))‖) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s => ∑ q : Fin n → Fin 3,
        ‖A s (fun i => basisVector (q i))-A t (fun i => basisVector (q i))‖) :=
      continuous_finset_sum Finset.univ (fun q _ => ((hA q).sub continuous_const).norm)
    simpa only [sub_self,norm_zero,Finset.sum_const_zero] using
      hc.continuousAt.tendsto (x := t)
  exact squeeze_zero (fun s => norm_nonneg (A s-A t))
    (fun s => tensor_norm_le_sum_basis (A s-A t)) h

theorem continuous_postcomposition {n : ℕ} (S : T → F →L[ℝ] G)
    (hS : ∀ f : F,Continuous (fun t => S t f))
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin 3 → ℝ) F) :
    Continuous (fun t => (S t).compContinuousMultilinearMap A) := by
  apply continuous_of_basis
  intro q
  exact hS (A (fun i => basisVector (q i)))

end
end Resonance.FiniteTensorContinuity

#check Resonance.FiniteTensorContinuity.sum_basis
#check Resonance.FiniteTensorContinuity.tensor_basis_expansion
#check Resonance.FiniteTensorContinuity.tensor_norm_le_sum_basis
#check Resonance.FiniteTensorContinuity.continuous_of_basis
#check Resonance.FiniteTensorContinuity.continuous_postcomposition
#print axioms Resonance.FiniteTensorContinuity.sum_basis
#print axioms Resonance.FiniteTensorContinuity.tensor_basis_expansion
#print axioms Resonance.FiniteTensorContinuity.tensor_norm_le_sum_basis
#print axioms Resonance.FiniteTensorContinuity.continuous_of_basis
#print axioms Resonance.FiniteTensorContinuity.continuous_postcomposition
