import Resonance.StrongCellParameterContinuity

/-! Bounded scalar multiplication on the original ambient cube L-infinity
classes, including the quantitative difference estimate. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CubeLinftyMultiplier
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure ActualPairNormalization

def vector {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R))
    (f : Lp ℝ ∞ (cubeVolume R)) : Lp ℝ ∞ (cubeVolume R) :=
  (hw.mul' (Lp.memLp f)).toLp (fun k=>f k*w k)

theorem vector_ae {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R))
    (f : Lp ℝ ∞ (cubeVolume R)) :
    vector hw f=ᵐ[cubeVolume R] (fun k=>f k*w k) := MemLp.coeFn_toLp _

theorem vector_add {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R))
    (f g : Lp ℝ ∞ (cubeVolume R)) : vector hw (f+g)=vector hw f+vector hw g := by
  apply Lp.ext
  filter_upwards [vector_ae hw (f+g),vector_ae hw f,vector_ae hw g,Lp.coeFn_add f g,
    Lp.coeFn_add (vector hw f) (vector hw g)] with k hfg hf hg hi ho
  simp only [Pi.add_apply] at hi ho
  rw [hfg,ho,hi,hf,hg,add_mul]

theorem vector_smul {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R))
    (c : ℝ) (f : Lp ℝ ∞ (cubeVolume R)) : vector hw (c • f)=c • vector hw f := by
  apply Lp.ext
  filter_upwards [vector_ae hw (c • f),vector_ae hw f,Lp.coeFn_smul c f,
    Lp.coeFn_smul c (vector hw f)] with k hcf hf hi ho
  simp only [Pi.smul_apply,smul_eq_mul] at hi ho
  rw [hcf,ho,hi,hf,mul_assoc]

theorem vector_bound {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R))
    {C : ℝ} (hC : 0≤C) (hb : ∀ᵐk∂cubeVolume R,‖w k‖≤C)
    (f : Lp ℝ ∞ (cubeVolume R)) : ‖vector hw f‖≤C*‖f‖ := by
  letI := cubeVolume_finite R
  have hAE : ∀ᵐk∂cubeVolume R,‖vector hw f k‖≤C*‖f‖ := by
    filter_upwards [vector_ae hw f,LinftyRowOperator.ae_norm_bound f,hb] with k he hf hk
    rw [he,norm_mul]
    exact (mul_le_mul hf hk (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  simpa using Lp.norm_le_of_ae_bound (mul_nonneg hC (norm_nonneg _)) hAE

def linear {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R)) :
    Lp ℝ ∞ (cubeVolume R)→ₗ[ℝ]Lp ℝ ∞ (cubeVolume R) where
  toFun := vector hw
  map_add' := vector_add hw
  map_smul' := vector_smul hw

def operator {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R)) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (linear hw).mkContinuous (LpOperators.multiplierNorm w (cubeVolume R))
    (vector_bound hw ENNReal.toReal_nonneg (LpOperators.multiplier_ae_bound hw))

theorem operator_ae {R : ℝ} {w : E→ℝ} (hw : MemLp w ∞ (cubeVolume R))
    (f : Lp ℝ ∞ (cubeVolume R)) :
    operator hw f=ᵐ[cubeVolume R] (fun k=>f k*w k) := vector_ae hw f

theorem operator_difference_bound {R : ℝ} {v w : E→ℝ}
    (hv : MemLp v ∞ (cubeVolume R)) (hw : MemLp w ∞ (cubeVolume R))
    {C : ℝ} (hC : 0≤C) (hb : ∀ᵐk∂cubeVolume R,‖v k-w k‖≤C) :
    ‖operator hv-operator hw‖≤C := by
  letI := cubeVolume_finite R
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hAE : ∀ᵐk∂cubeVolume R,‖((operator hv-operator hw) f) k‖≤C*‖f‖ := by
    filter_upwards [operator_ae hv f,operator_ae hw f,Lp.coeFn_sub (operator hv f) (operator hw f),
      LinftyRowOperator.ae_norm_bound f,hb] with k hvk hwk hs hf hk
    change (operator hv f-operator hw f) k=(operator hv f) k-(operator hw f) k at hs
    change ‖(operator hv f-operator hw f) k‖≤_
    rw [hs,hvk,hwk,←mul_sub,norm_mul]
    exact (mul_le_mul hf hk (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  simpa using Lp.norm_le_of_ae_bound (mul_nonneg hC (norm_nonneg _)) hAE

end
end Resonance.CubeLinftyMultiplier
