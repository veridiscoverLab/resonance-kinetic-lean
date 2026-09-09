import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! A genuine bounded operator on the completed common square-summable
coefficient space, constructed from one uniformly bounded family. -/
open ContinuousLinearMap
open scoped ENNReal
namespace Resonance.L2DiagonalOperator
noncomputable section
variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev Space (I E : Type*) [NormedAddCommGroup E] := lp (fun _ : I=>E) 2

omit [NormedSpace ℂ E] in
theorem hasSum_norm_square (v : Space I E) :
    HasSum (fun i=>‖v i‖^2) (‖v‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) v

theorem mapped_mem (T : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C) (hT : ∀i,‖T i‖≤C)
    (v : Space I E) : Memℓp (fun i=>T i (v i)) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun i=>sq_nonneg _) _
    ((hasSum_norm_square v).summable.mul_left (C^2))
  intro i
  have hh : ‖T i (v i)‖≤C*‖v i‖ :=
    (T i).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr hh
  simpa only [mul_pow] using hs

def mapLinear (T : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C) (hT : ∀i,‖T i‖≤C) :
    Space I E→ₗ[ℂ]Space I E where
  toFun v:=⟨fun i=>T i (v i),mapped_mem T hC hT v⟩
  map_add' v w:=by ext i; exact map_add (T i) _ _
  map_smul' a v:=by ext i; exact map_smul (T i) _ _

theorem mapLinear_apply (T : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C) (hT : ∀i,‖T i‖≤C)
    (v : Space I E) (i : I) : mapLinear T hC hT v i=T i (v i) := rfl

theorem mapLinear_norm (T : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C) (hT : ∀i,‖T i‖≤C)
    (v : Space I E) : ‖mapLinear T hC hT v‖≤C*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  have hh : ∑'i,‖mapLinear T hC hT v i‖^2≤∑'i,C^2*‖v i‖^2 := by
    apply Summable.tsum_le_tsum _ (hasSum_norm_square _).summable
      ((hasSum_norm_square v).summable.mul_left (C^2))
    intro i
    have hb : ‖T i (v i)‖≤C*‖v i‖ :=
      (T i).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr hb
    simpa only [mapLinear_apply,mul_pow] using hs
  rw [(hasSum_norm_square _).tsum_eq,tsum_mul_left,(hasSum_norm_square v).tsum_eq] at hh
  simpa only [mul_pow] using hh

def diagonal (T : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C) (hT : ∀i,‖T i‖≤C) :
    Space I E→L[ℂ]Space I E := (mapLinear T hC hT).mkContinuous C (mapLinear_norm T hC hT)

theorem diagonal_apply (T : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C) (hT : ∀i,‖T i‖≤C)
    (v : Space I E) (i : I) : diagonal T hC hT v i=T i (v i) := rfl

theorem diagonal_norm (T : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C) (hT : ∀i,‖T i‖≤C) :
    ‖diagonal T hC hT‖≤C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact mapLinear_norm T hC hT

end
end Resonance.L2DiagonalOperator
