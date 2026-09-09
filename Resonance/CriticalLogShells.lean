import Resonance.CornerFrequencyBounds
import Mathlib.Analysis.PSeries

/-! The critical inverse-frequency summation.  The abstract measure
estimate below is separated from its actual cube-volume instance. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CriticalLogShells
noncomputable section
set_option maxHeartbeats 800000

def shellRadius (n:ℕ) : ℝ := Real.exp (-((n:ℝ)+8))
def shell (e:α→ℝ) (n:ℕ) : Set α :=
  {x|shellRadius (n+1)<e x ∧ e x≤ shellRadius n}
def smallLayer (e:α→ℝ) : Set α := {x|0<e x ∧ e x≤Real.exp (-8)}

theorem shellRadius_pos (n:ℕ) : 0<shellRadius n := Real.exp_pos _
theorem shellRadius_le_cutoff (n:ℕ) : shellRadius n≤Real.exp (-8) := by
  apply Real.exp_le_exp.mpr
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  linarith

theorem exp_cutoff_le : Real.exp (-8)≤(1:ℝ)/256 := by
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
  have hlog : Real.log ((1:ℝ)/256)= -8*Real.log 2 := by
    rw [show (1:ℝ)/256=(2^8)⁻¹ by norm_num,Real.log_inv,Real.log_pow]
    norm_num
  rw [←Real.exp_log (by norm_num:(0:ℝ)<1/256)]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  norm_num at hlog2
  linarith

theorem scalar_shell_cover {x:ℝ} (hx0:0<x) (hx1:x≤Real.exp (-8)) :
    ∃n:ℕ,shellRadius (n+1)<x ∧ x≤ shellRadius n := by
  have hlog := Real.log_le_log hx0 hx1
  rw [Real.log_exp] at hlog
  have hn0 : 0≤ -Real.log x-8 := by linarith
  let n : ℕ := Nat.floor (-Real.log x-8)
  have hnlo := Nat.floor_le hn0
  have hnhi := Nat.lt_floor_add_one (-Real.log x-8)
  refine ⟨n,?_,?_⟩
  · rw [←Real.exp_log hx0]
    apply Real.exp_lt_exp.mpr
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp [n]
    linarith
  · rw [←Real.exp_log hx0]
    apply Real.exp_le_exp.mpr
    change Real.log x≤ -((n:ℝ)+8)
    dsimp [n]
    linarith

theorem smallLayer_eq_union (e:α→ℝ) : smallLayer e=⋃n:ℕ,shell e n := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := scalar_shell_cover hx.1 hx.2
    exact mem_iUnion.mpr ⟨n,hn⟩
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact ⟨(shellRadius_pos (n+1)).trans hn.1,hn.2.trans (shellRadius_le_cutoff n)⟩

def inverseEnvelope (c:ℝ) (n:ℕ) : ℝ :=
  c^(-(3:ℝ)/2)*Real.exp (3*((n:ℝ)+9))/((n:ℝ)+8)^3

theorem shell_inverse_bound {c e v:ℝ} (hc:0<c) (n:ℕ)
    (hel:shellRadius (n+1)<e) (heu:e≤ shellRadius n)
    (hν:c*e^2*(Real.log (1/e))^2≤v) :
    v^(-(3:ℝ)/2)≤ inverseEnvelope c n := by
  have he0 : 0<e := (shellRadius_pos (n+1)).trans hel
  have hq : 0<(n:ℝ)+8 := by positivity
  have hlog : (n:ℝ)+8≤Real.log (1/e) := by
    have hh := Real.log_le_log he0 heu
    rw [shellRadius,Real.log_exp] at hh
    rw [one_div,Real.log_inv]
    linarith
  have he2 : Real.exp (-2*((n:ℝ)+9))≤e^2 := by
    have hh : (shellRadius (n+1))^2=Real.exp (-2*((n:ℝ)+9)) := by
      simp only [shellRadius,Nat.cast_add,Nat.cast_one,pow_two,←Real.exp_add]
      congr 1
      ring
    rw [←hh]
    nlinarith [shellRadius_pos (n+1)]
  have hl2 : ((n:ℝ)+8)^2≤(Real.log (1/e))^2 := by nlinarith
  have hlo : c*Real.exp (-2*((n:ℝ)+9))*((n:ℝ)+8)^2≤v := by
    apply le_trans _ hν
    exact mul_le_mul (mul_le_mul_of_nonneg_left he2 hc.le) hl2 (sq_nonneg _) (by positivity)
  have hb0 : 0<c*Real.exp (-2*((n:ℝ)+9))*((n:ℝ)+8)^2 := by positivity
  have hr := Real.rpow_le_rpow_of_nonpos hb0 hlo (by norm_num:-(3:ℝ)/2≤0)
  have hpow : (c*Real.exp (-2*((n:ℝ)+9))*((n:ℝ)+8)^2)^(-(3:ℝ)/2)=
      inverseEnvelope c n := by
    rw [Real.mul_rpow (by positivity) (sq_nonneg _),Real.mul_rpow hc.le (by positivity),
      ←Real.exp_mul,←Real.rpow_natCast_mul hq.le 2 (-(3:ℝ)/2)]
    norm_num only [show (2:ℝ)*(-(3:ℝ)/2)= -3 by norm_num]
    rw [show -(2:ℝ)*((n:ℝ)+9)* -((3:ℝ)/2)=3*((n:ℝ)+9) by ring]
    rw [show (-3:ℝ)= -(3:ℝ) by rfl,Real.rpow_neg hq.le,Real.rpow_ofNat]
    simp only [inverseEnvelope,div_eq_mul_inv,neg_mul]
  exact hr.trans_eq hpow

theorem inverseEnvelope_nonnegative {c:ℝ} (hc:0<c) (n:ℕ) :
    0≤ inverseEnvelope c n := by unfold inverseEnvelope; positivity

theorem shell_cost_identity {c C:ℝ} (hc:0<c) (n:ℕ) :
    ENNReal.ofReal (inverseEnvelope c n)*ENNReal.ofReal (C*(shellRadius n)^3)=
      ENNReal.ofReal (C*c^(-(3:ℝ)/2)*Real.exp 3/((n:ℝ)+8)^3) := by
  rw [←ENNReal.ofReal_mul (inverseEnvelope_nonnegative hc n)]
  congr 1
  have hexp : Real.exp (3*((n:ℝ)+9))*(shellRadius n)^3=Real.exp 3 := by
    unfold shellRadius
    rw [←Real.exp_nat_mul,←Real.exp_add]
    norm_num
    ring
  calc
    _ = C*c^(-(3:ℝ)/2)*(Real.exp (3*((n:ℝ)+9))*(shellRadius n)^3)/((n:ℝ)+8)^3 := by
      unfold inverseEnvelope
      ring
    _ = _ := by rw [hexp]

theorem critical_cost_summable (c C:ℝ) :
    Summable (fun n:ℕ=>C*c^(-(3:ℝ)/2)*Real.exp 3/((n:ℝ)+8)^3) := by
  have h := (Real.summable_one_div_nat_add_rpow 8 3).mpr (by norm_num)
  have hh : Summable (fun n:ℕ=>1/((n:ℝ)+8)^3) := by
    have he (n:ℕ) : |(n:ℝ)+8|=(n:ℝ)+8 := abs_of_nonneg (by positivity)
    simpa only [he,Real.rpow_ofNat] using h
  simpa only [mul_one_div] using hh.mul_left (C*c^(-(3:ℝ)/2)*Real.exp 3)

/-- Critical exponent 3/2 from a proved cubic layer-volume bound.
The actual cube instance is supplied separately; this theorem does not
assume integrability, a spectral gap, or a finite inverse moment. -/
theorem small_layer_critical_integral_finite {α:Type*} [MeasurableSpace α]
    (μ:Measure α) (e ν:α→ℝ) (he:Measurable e) {c C:ℝ} (hc:0<c) (_hC:0≤C)
    (hvol:∀ r:ℝ, 0<r → r≤Real.exp (-8) →
      μ {x|0<e x ∧ e x≤r}≤ENNReal.ofReal (C*r^3))
    (hν:∀ᵐx∂μ,x∈smallLayer e→c*(e x)^2*(Real.log (1/e x))^2≤ν x) :
    (∫⁻x in smallLayer e,ENNReal.ofReal ((ν x)^(-(3:ℝ)/2)) ∂μ)<∞ := by
  have hshell (n:ℕ) : MeasurableSet (shell e n) :=
    (measurableSet_lt measurable_const he).inter (measurableSet_le he measurable_const)
  have hterm (n:ℕ) :
      (∫⁻x in shell e n,ENNReal.ofReal ((ν x)^(-(3:ℝ)/2)) ∂μ)≤
      ENNReal.ofReal (C*c^(-(3:ℝ)/2)*Real.exp 3/((n:ℝ)+8)^3) := by
    have hpoint : ∀ᵐx∂μ.restrict (shell e n),
        ENNReal.ofReal ((ν x)^(-(3:ℝ)/2))≤ENNReal.ofReal (inverseEnvelope c n) := by
      filter_upwards [ae_restrict_mem (hshell n),ae_restrict_of_ae hν] with x hx hnx
      have hsmall : x∈smallLayer e :=
        ⟨(shellRadius_pos (n+1)).trans hx.1,hx.2.trans (shellRadius_le_cutoff n)⟩
      exact ENNReal.ofReal_le_ofReal (shell_inverse_bound hc n hx.1 hx.2 (hnx hsmall))
    have hv : μ (shell e n)≤ENNReal.ofReal (C*(shellRadius n)^3) := by
      apply (measure_mono (show shell e n⊆{x|0<e x ∧ e x≤ shellRadius n} from
        fun x hx=>⟨(shellRadius_pos (n+1)).trans hx.1,hx.2⟩)).trans
      exact hvol _ (shellRadius_pos n) (shellRadius_le_cutoff n)
    calc
      _ ≤ ∫⁻x in shell e n,ENNReal.ofReal (inverseEnvelope c n) ∂μ := lintegral_mono_ae hpoint
      _ = ENNReal.ofReal (inverseEnvelope c n)*μ (shell e n) := by
        rw [lintegral_const,Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (inverseEnvelope c n)*ENNReal.ofReal (C*(shellRadius n)^3) :=
        mul_le_mul_right hv _
      _ = _ := shell_cost_identity hc n
  rw [smallLayer_eq_union]
  apply lt_of_le_of_lt (lintegral_iUnion_le _ _)
  exact lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) (critical_cost_summable c C).tsum_ofReal_lt_top

end
end Resonance.CriticalLogShells
