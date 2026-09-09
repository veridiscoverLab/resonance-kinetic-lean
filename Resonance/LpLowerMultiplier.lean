import Resonance.LpFixedTestOperators

/-! A positive lower bound permits removing an actual L² multiplier.
The unknown vector is never used as a fixed-test convergence input. -/
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.LpLowerMultiplier
open LpOperators
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} {l : Filter ι}

theorem multiply_lower_bound {b : A → ℝ} (hb : MemLp b ∞ μ)
    {m : ℝ} (hm : 0 ≤ m) (hl : ∀ᵐ x ∂μ, m ≤ |b x|) (u : Lp ℝ 2 μ) :
    m * ‖u‖ ≤ ‖multiplyCLM hb u‖ := by
  have h : ‖m • u‖ ≤ ‖multiplyCLM hb u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul m u,multiply_ae hb u,hl] with x hs hx hl
    change ‖(m • u) x‖ ≤ ‖multiply hb u x‖
    rw [hs,hx]
    simpa only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg hm,mul_comm] using
      mul_le_mul_of_nonneg_right hl (norm_nonneg (u x))
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm] using h

theorem remove_moving_multiplier {b : ι → A → ℝ}
    (hb : ∀ n, MemLp (b n) ∞ μ) {m : ℝ} (hm : 0 < m)
    (hl : ∀ n, ∀ᵐ x ∂μ, m ≤ |b n x|)
    {v : ι → Lp ℝ 2 μ} {u : Lp ℝ 2 μ}
    (hcurrent : Tendsto (fun n => multiplyCLM (hb n) (v n)) l (𝓝 u))
    (hfixed : Tendsto (fun n => multiplyCLM (hb n) u) l (𝓝 u)) :
    Tendsto v l (𝓝 u) := by
  have hz := hcurrent.sub hfixed
  have hn : Tendsto (fun n => ‖multiplyCLM (hb n) (v n-u)‖) l (𝓝 0) := by
    simpa only [map_sub,sub_self,norm_zero] using hz.norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hle : ∀ n, ‖v n-u‖ ≤ m⁻¹ * ‖multiplyCLM (hb n) (v n-u)‖ := by
    intro n
    have h := multiply_lower_bound (hb n) hm.le (hl n) (v n-u)
    rw [mul_comm m⁻¹,←div_eq_mul_inv]
    exact (le_div_iff₀ hm).2 (by simpa only [mul_comm] using h)
  exact squeeze_zero (fun n => norm_nonneg _) hle (by simpa using hn.const_mul m⁻¹)

end Resonance.LpLowerMultiplier
