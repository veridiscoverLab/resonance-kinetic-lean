import Resonance.LpOperators
import Resonance.FixedMultiplier

/-! Actual real L² multiplication operators converge on each fixed complete
test under bounded convergence in measure. The operator norm is bounded,
but operator-norm convergence and strong convergence on moving vectors are
not asserted. All integral identities use actual L² inner products. -/
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.LpFixedTestOperators
open LpOperators
variable {A ι : Type*} [MeasurableSpace A] {μ σ : Measure A}
variable {l : Filter ι} [l.IsCountablyGenerated]

theorem multiply_uniform_bound {w : A→ℝ} (hw : MemLp w ∞ σ)
    {C : ℝ} (hb : ∀ᵐ x ∂σ, |w x|≤C) (f : Lp ℝ 2 σ) :
    ‖multiplyCLM hw f‖≤C*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae hw f,hb] with x hx hb
  change ‖multiply hw f x‖≤C*‖f x‖
  rw [hx]
  simp only [norm_mul,Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg (f x))]

theorem multiply_norm_bound {w : A→ℝ} (hw : MemLp w ∞ σ)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᵐ x ∂σ, |w x|≤C) :
    ‖multiplyCLM hw‖≤C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (multiply_uniform_bound hw hb)

theorem multiply_symmetric {w : A→ℝ} (hw : MemLp w ∞ σ)
    (f g : Lp ℝ 2 σ) :
    inner ℝ (multiplyCLM hw f) g = inner ℝ f (multiplyCLM hw g) := by
  change (∫ x,inner ℝ (multiply hw f x) (g x) ∂σ) =
    ∫ x,inner ℝ (f x) (multiply hw g x) ∂σ
  apply integral_congr_ae
  filter_upwards [multiply_ae hw f,multiply_ae hw g] with x hf hg
  rw [hf,hg]
  change (g x)*(f x*w x)=(g x*w x)*(f x)
  ring

theorem multiply_eq_id {w : A→ℝ} (hw : MemLp w ∞ σ)
    (hone : w=ᵐ[σ](fun _=>1)) : multiplyCLM hw=1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [multiply_ae hw f,hone] with x hx h1
  change multiply hw f x=f x
  rw [hx,h1,mul_one]

theorem fixed_test_strong {b : ι→A→ℝ} {c : A→ℝ}
    (hb : ∀ n,MemLp (b n) ∞ σ) (hc : MemLp c ∞ σ)
    {C : ℝ} (hbnd : ∀ n,∀ᵐ x ∂σ,|b n x|≤C)
    (hcnd : ∀ᵐ x ∂σ,|c x|≤C)
    (hac : σ≪μ) (hconv : TendstoInMeasure μ b l c)
    (V : Lp ℝ 2 σ) :
    Tendsto (fun n=>multiplyCLM (hb n) V) l (𝓝 (multiplyCLM hc V)) := by
  obtain ⟨G,hG,hlim⟩:=FixedMultiplier.fixed_multiplier_strong hac hconv
    (fun n=>(hb n).aestronglyMeasurable) hc.aestronglyMeasurable hbnd hcnd (Lp.memLp V)
  have heq : (fun n=>multiplyCLM (hb n) V-multiplyCLM hc V)=G := by
    funext n
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (multiplyCLM (hb n) V) (multiplyCLM hc V),
      multiply_ae (hb n) V,multiply_ae hc V,hG n] with x hsub hbn hcn hg
    change (multiplyCLM (hb n) V-multiplyCLM hc V) x=G n x
    rw [hsub,hg]
    change multiply (hb n) V x-multiply hc V x=(b n x-c x)*V x
    rw [hbn,hcn]
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh:=tendsto_zero_iff_norm_tendsto_zero.mp (heq ▸ hlim)
  exact hh

end Resonance.LpFixedTestOperators
