import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic

/-! Actual bounded diagonal linear maps on arbitrary supremum families.
The index set need not be finite or compact. -/
open Set
open scoped ENNReal
namespace Resonance.SupFamilyLinear
noncomputable section
variable {I : Type*} {E F : I→Type*}
  [∀i,NormedAddCommGroup (E i)] [∀i,NormedSpace ℝ (E i)]
  [∀i,NormedAddCommGroup (F i)] [∀i,NormedSpace ℝ (F i)]

def diagonalLinear (A : ∀i,E i→L[ℝ]F i) {C : ℝ}
    (hC : 0≤C) (hA : ∀i,‖A i‖≤C) : lp E ∞→ₗ[ℝ]lp F ∞ where
  toFun u := ⟨fun i => A i (u i),memℓp_infty ⟨C*‖u‖,by
    rintro _ ⟨i,rfl⟩
    exact ((A i).le_opNorm (u i)).trans
      (mul_le_mul (hA i) (lp.norm_apply_le_norm ENNReal.top_ne_zero u i)
        (norm_nonneg _) hC)⟩⟩
  map_add' u v := by apply lp.ext; funext i; exact map_add (A i) (u i) (v i)
  map_smul' c u := by apply lp.ext; funext i; exact map_smul (A i) c (u i)

def diagonal (A : ∀i,E i→L[ℝ]F i) {C : ℝ}
    (hC : 0≤C) (hA : ∀i,‖A i‖≤C) : lp E ∞→L[ℝ]lp F ∞ :=
  (diagonalLinear A hC hA).mkContinuous C (fun u =>
    lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg u)) (fun i =>
      ((A i).le_opNorm (u i)).trans
        (mul_le_mul (hA i) (lp.norm_apply_le_norm ENNReal.top_ne_zero u i)
          (norm_nonneg _) hC)))

theorem diagonal_apply (A : ∀i,E i→L[ℝ]F i) {C : ℝ}
    (hC : 0≤C) (hA : ∀i,‖A i‖≤C) (u : lp E ∞) (i : I) :
    diagonal A hC hA u i=A i (u i) := rfl

def isometryLinear (J : ∀i,E i→ₗᵢ[ℝ]F i) : lp E ∞→ₗ[ℝ]lp F ∞ :=
  diagonalLinear (fun i => (J i).toContinuousLinearMap) zero_le_one
    (fun i => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      simp)

def isometry (J : ∀i,E i→ₗᵢ[ℝ]F i) : lp E ∞→ₗᵢ[ℝ]lp F ∞ where
  toLinearMap := isometryLinear J
  norm_map' u := by
    apply le_antisymm
    · apply lp.norm_le_of_forall_le (norm_nonneg u)
      intro i
      change ‖J i (u i)‖≤‖u‖
      rw [(J i).norm_map]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero u i
    · apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro i
      rw [←(J i).norm_map (u i)]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (isometryLinear J u) i

theorem isometry_apply (J : ∀i,E i→ₗᵢ[ℝ]F i) (u : lp E ∞) (i : I) :
    isometry J u i=J i (u i) := rfl

end
end Resonance.SupFamilyLinear
