import Resonance.ContinuousRowMultiplier
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Uniform removal of a bounded monotone input multiplier from a compact
family of actual L1 rows. No operator-norm convergence of that multiplier
on L-infinity is assumed. -/
open MeasureTheory Set Filter
open scoped Topology
namespace Resonance.MonotoneRowVanishing
noncomputable section
set_option maxHeartbeats 1200000
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace Y] {μ : Measure Y}

theorem uniform_row_vanishing (K : X→Y→ℝ)
    (hi : ∀x,Integrable (K x) μ)
    (hc : ∀x,Tendsto (fun a=>∫y,‖K a y-K x y‖∂μ) (𝓝 x) (𝓝 0))
    (hK : ∀x,0≤ᵐ[μ]K x)
    (m : ℕ→Y→ℝ) (hm : ∀n,AEStronglyMeasurable (m n) μ)
    (hb : ∀n,∀ᵐy∂μ,0≤m n y ∧ m n y≤1)
    (ha : ∀n l,n≤l → ∀ᵐy∂μ,m l y≤m n y)
    (ht : ∀ᵐy∂μ,Tendsto (fun n=>m n y) atTop (𝓝 0)) :
    TendstoUniformly (fun n x=>∫y,K x y*m n y∂μ) (fun _=>0) atTop := by
  have hnorm (n : ℕ) : ∀ᵐy∂μ,‖m n y‖≤1 := by
    filter_upwards [hb n] with y hy
    rw [Real.norm_of_nonneg hy.1]
    exact hy.2
  have hi' (n : ℕ) (x : X) : Integrable (fun y=>K x y*m n y) μ :=
    (hi x).mul_bdd (hm n) (hnorm n)
  have he (n : ℕ) (x : X) : (∫y,‖K x y*m n y‖∂μ)=∫y,K x y*m n y∂μ := by
    apply integral_congr_ae
    filter_upwards [hK x,hb n] with y hk hy
    exact Real.norm_of_nonneg (mul_nonneg hk hy.1)
  have hcont (n : ℕ) : Continuous (fun x=>∫y,K x y*m n y∂μ) := by
    have hh := ContinuousRowOperator.rowNorm_continuous (fun x y=>K x y*m n y) (hi' n)
      (ContinuousRowMultiplier.mul_rows_L1_continuous K hi hc (m n) (hm n) zero_le_one (hnorm n))
    simpa only [he] using hh
  have hanti : Antitone (fun n x=>∫y,K x y*m n y∂μ) := by
    intro n l hnl x
    apply integral_mono_ae (hi' l x) (hi' n x)
    filter_upwards [ha n l hnl,hK x] with y hy hk
    exact mul_le_mul_of_nonneg_left hy hk
  apply Antitone.tendstoUniformly_of_forall_tendsto hcont hanti continuous_const
  intro x
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ:=μ) (l:=atTop) (F:=fun n y=>K x y*m n y) (f:=fun _=>0) (fun y=>‖K x y‖)
  have he0 : (∫y,(0:ℝ)∂μ)=0 := integral_zero _ _
  rw [←he0]
  apply hh
  · exact Eventually.of_forall (fun n=>(hi' n x).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro n
    filter_upwards [hnorm n] with y hy
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy (norm_nonneg (K x y))
  · exact (hi x).norm
  · filter_upwards [ht] with y hy
    simpa only [mul_zero] using (tendsto_const_nhds (x:=K x y)).mul hy

end
end Resonance.MonotoneRowVanishing
