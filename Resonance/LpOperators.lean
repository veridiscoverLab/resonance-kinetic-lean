import Mathlib

/-! Representative-preserving bounded multipliers and changes of measure on
real L². Model-specific applications must supply the actual weight and the
actual domination; neither is an axiom or a substitute for a collision form. -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.LpOperators
noncomputable section
variable {A : Type*} [MeasurableSpace A] {μ ν : Measure A}

def multiplierNorm (w : A → ℝ) (μ : Measure A) : ℝ := (eLpNorm w ∞ μ).toReal

theorem multiplier_ae_bound {w : A → ℝ} (hw : MemLp w ∞ μ) :
    ∀ᵐ x ∂μ, ‖w x‖ ≤ multiplierNorm w μ := by
  have ht : eLpNormEssSup w μ ≠ ∞ := by simpa only [eLpNorm_exponent_top] using hw.2.ne
  filter_upwards [enorm_ae_le_eLpNormEssSup w μ] with x hx
  have h := ENNReal.toReal_mono ht hx
  simpa only [toReal_enorm, multiplierNorm, eLpNorm_exponent_top] using h

def multiply {w : A → ℝ} (hw : MemLp w ∞ μ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (hw.mul' (Lp.memLp f)).toLp (fun x => f x * w x)

theorem multiply_ae {w : A → ℝ} (hw : MemLp w ∞ μ) (f : Lp ℝ 2 μ) :
    multiply hw f =ᵐ[μ] (fun x => f x * w x) := MemLp.coeFn_toLp _

theorem multiply_add {w : A → ℝ} (hw : MemLp w ∞ μ) (f g : Lp ℝ 2 μ) :
    multiply hw (f+g) = multiply hw f + multiply hw g := by
  apply Lp.ext
  filter_upwards [multiply_ae hw (f+g), multiply_ae hw f, multiply_ae hw g,
    Lp.coeFn_add f g, Lp.coeFn_add (multiply hw f) (multiply hw g)] with x hfg hf hg hin hout
  simp only [Pi.add_apply] at hin hout
  rw [hfg, hout, hin, hf, hg]
  ring

theorem multiply_smul {w : A → ℝ} (hw : MemLp w ∞ μ) (a : ℝ) (f : Lp ℝ 2 μ) :
    multiply hw (a • f) = a • multiply hw f := by
  apply Lp.ext
  filter_upwards [multiply_ae hw (a • f), multiply_ae hw f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (multiply hw f)] with x haf hf hin hout
  simp only [Pi.smul_apply, smul_eq_mul] at hin hout
  rw [haf, hout, hin, hf]
  ring

theorem multiply_bound {w : A → ℝ} (hw : MemLp w ∞ μ) (f : Lp ℝ 2 μ) :
    ‖multiply hw f‖ ≤ multiplierNorm w μ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae hw f, multiplier_ae_bound hw] with x hx hwx
  rw [hx, norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left hwx (norm_nonneg (f x))]

def multiplyLinear {w : A → ℝ} (hw : MemLp w ∞ μ) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := multiply hw
  map_add' := multiply_add hw
  map_smul' := multiply_smul hw

def multiplyCLM {w : A → ℝ} (hw : MemLp w ∞ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (multiplyLinear hw).mkContinuous (multiplierNorm w μ) (multiply_bound hw)

def changeNorm (C : ℝ≥0∞) : ℝ := (C ^ (1 / 2 : ℝ)).toReal

def changeMeasure {C : ℝ≥0∞} (hC : C ≠ ∞) (hm : ν ≤ C • μ) (f : Lp ℝ 2 μ) : Lp ℝ 2 ν :=
  ((Lp.memLp f).of_measure_le_smul hC hm).toLp f

theorem changeMeasure_ae {C : ℝ≥0∞} (hC : C ≠ ∞) (hm : ν ≤ C • μ) (f : Lp ℝ 2 μ) :
    changeMeasure hC hm f =ᵐ[ν] f := MemLp.coeFn_toLp _

theorem changeMeasure_add {C : ℝ≥0∞} (hC : C ≠ ∞) (hm : ν ≤ C • μ) (f g : Lp ℝ 2 μ) :
    changeMeasure hC hm (f+g) = changeMeasure hC hm f + changeMeasure hC hm g := by
  apply Lp.ext
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hm
  filter_upwards [changeMeasure_ae hC hm (f+g), changeMeasure_ae hC hm f,
    changeMeasure_ae hC hm g, Lp.coeFn_add (changeMeasure hC hm f) (changeMeasure hC hm g),
    hac.ae_eq (Lp.coeFn_add f g)] with x hfg hf hg hout hin
  simp only [Pi.add_apply] at hout hin
  rw [hfg, hout, hin, hf, hg]

theorem changeMeasure_smul {C : ℝ≥0∞} (hC : C ≠ ∞) (hm : ν ≤ C • μ) (a : ℝ) (f : Lp ℝ 2 μ) :
    changeMeasure hC hm (a • f) = a • changeMeasure hC hm f := by
  apply Lp.ext
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hm
  filter_upwards [changeMeasure_ae hC hm (a • f), changeMeasure_ae hC hm f,
    Lp.coeFn_smul a (changeMeasure hC hm f), hac.ae_eq (Lp.coeFn_smul a f)] with x haf hf hout hin
  simp only [Pi.smul_apply] at hout hin
  rw [haf, hout, hin, hf]

theorem changeMeasure_bound {C : ℝ≥0∞} (hC : C ≠ ∞) (hm : ν ≤ C • μ) (f : Lp ℝ 2 μ) :
    ‖changeMeasure hC hm f‖ ≤ changeNorm C * ‖f‖ := by
  have hmono := eLpNorm_mono_measure (p := 2) f hm
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at hmono
  norm_num at hmono
  have ht : C ^ (1 / 2 : ℝ) * eLpNorm f 2 μ < ∞ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC) (Lp.memLp f).2
  have hr := ENNReal.toReal_mono ht.ne hmono
  rw [ENNReal.toReal_mul] at hr
  unfold changeMeasure
  rw [Lp.norm_toLp]
  exact hr

def changeLinear {C : ℝ≥0∞} (hC : C ≠ ∞) (hm : ν ≤ C • μ) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν where
  toFun := changeMeasure hC hm
  map_add' := changeMeasure_add hC hm
  map_smul' := changeMeasure_smul hC hm

def changeCLM {C : ℝ≥0∞} (hC : C ≠ ∞) (hm : ν ≤ C • μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  (changeLinear hC hm).mkContinuous (changeNorm C) (changeMeasure_bound hC hm)

end
end Resonance.LpOperators
