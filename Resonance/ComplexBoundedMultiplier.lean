import Mathlib

/-! Bounded multiplication in the original complex L2 space, with
representatives and inverse operators constructed from actual functions. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.ComplexBoundedMultiplier
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def vector {w : X→ℂ} (hw : MemLp w ∞ μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (hw.mul' (Lp.memLp f)).toLp (fun x=>f x*w x)

theorem vector_ae {w : X→ℂ} (hw : MemLp w ∞ μ) (f : Lp ℂ 2 μ) :
    vector hw f=ᵐ[μ] (fun x=>f x*w x) := MemLp.coeFn_toLp _

theorem vector_add {w : X→ℂ} (hw : MemLp w ∞ μ) (f g : Lp ℂ 2 μ) :
    vector hw (f+g)=vector hw f+vector hw g := by
  apply Lp.ext
  filter_upwards [vector_ae hw (f+g),vector_ae hw f,vector_ae hw g,Lp.coeFn_add f g,
    Lp.coeFn_add (vector hw f) (vector hw g)] with x hfg hf hg hi ho
  simp only [Pi.add_apply] at hi ho
  rw [hfg,ho,hi,hf,hg,add_mul]

theorem vector_smul {w : X→ℂ} (hw : MemLp w ∞ μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    vector hw (c • f)=c • vector hw f := by
  apply Lp.ext
  filter_upwards [vector_ae hw (c • f),vector_ae hw f,Lp.coeFn_smul c f,
    Lp.coeFn_smul c (vector hw f)] with x hcf hf hi ho
  simp only [Pi.smul_apply,smul_eq_mul] at hi ho
  rw [hcf,ho,hi,hf,mul_assoc]

theorem weight_ae_bound {w : X→ℂ} (hw : MemLp w ∞ μ) :
    ∀ᵐx∂μ,‖w x‖ ≤ (eLpNorm w ∞ μ).toReal := by
  have ht : eLpNormEssSup w μ≠∞ := by simpa only [eLpNorm_exponent_top] using hw.2.ne
  filter_upwards [enorm_ae_le_eLpNormEssSup w μ] with x hx
  have hh := ENNReal.toReal_mono ht hx
  simpa only [toReal_enorm,eLpNorm_exponent_top] using hh

theorem vector_bound {w : X→ℂ} (hw : MemLp w ∞ μ) {C : ℝ}
    (hb : ∀ᵐx∂μ,‖w x‖ ≤ C) (f : Lp ℂ 2 μ) : ‖vector hw f‖ ≤ C*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [vector_ae hw f,hb] with x hx hwx
  rw [hx,norm_mul]
  exact (mul_le_mul_of_nonneg_left hwx (norm_nonneg _)).trans_eq (mul_comm _ _)

def linear {w : X→ℂ} (hw : MemLp w ∞ μ) : Lp ℂ 2 μ→ₗ[ℂ]Lp ℂ 2 μ where
  toFun := vector hw
  map_add' := vector_add hw
  map_smul' := vector_smul hw

def operator {w : X→ℂ} (hw : MemLp w ∞ μ) : Lp ℂ 2 μ→L[ℂ]Lp ℂ 2 μ :=
  (linear hw).mkContinuous (eLpNorm w ∞ μ).toReal (vector_bound hw (weight_ae_bound hw))

theorem operator_ae {w : X→ℂ} (hw : MemLp w ∞ μ) (f : Lp ℂ 2 μ) :
    operator hw f=ᵐ[μ] (fun x=>f x*w x) := vector_ae hw f

theorem operator_inverse {w z : X→ℂ} (hw : MemLp w ∞ μ) (hz : MemLp z ∞ μ)
    (hprod : ∀ᵐx∂μ,w x*z x=1) (f : Lp ℂ 2 μ) :
    operator hw (operator hz f)=f := by
  apply Lp.ext
  filter_upwards [operator_ae hw (operator hz f),operator_ae hz f,hprod] with x ho hi hp
  rw [ho,hi,mul_assoc,mul_comm (z x) (w x),hp,mul_one]

def equivalence {w z : X→ℂ} (hw : MemLp w ∞ μ) (hz : MemLp z ∞ μ)
    (hprod : ∀ᵐx∂μ,w x*z x=1) : Lp ℂ 2 μ≃L[ℂ]Lp ℂ 2 μ where
  toLinearEquiv :=
    { (operator hw).toLinearMap with
      invFun := operator hz
      left_inv := operator_inverse hz hw (hprod.mono (fun x hx=>by rwa [mul_comm]))
      right_inv := operator_inverse hw hz hprod }
  continuous_toFun := (operator hw).continuous
  continuous_invFun := (operator hz).continuous

theorem equivalence_ae {w z : X→ℂ} (hw : MemLp w ∞ μ) (hz : MemLp z ∞ μ)
    (hprod : ∀ᵐx∂μ,w x*z x=1) (f : Lp ℂ 2 μ) :
    equivalence hw hz hprod f=ᵐ[μ] (fun x=>f x*w x) := operator_ae hw f

theorem inverse_equivalence_ae {w z : X→ℂ} (hw : MemLp w ∞ μ) (hz : MemLp z ∞ μ)
    (hprod : ∀ᵐx∂μ,w x*z x=1) (f : Lp ℂ 2 μ) :
    (equivalence hw hz hprod).symm f=ᵐ[μ] (fun x=>f x*z x) := operator_ae hz f

end
end Resonance.ComplexBoundedMultiplier
