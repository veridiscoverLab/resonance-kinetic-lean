import Resonance.HilbertSchmidtCompact
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! An operator represented by the actual L² kernel is its actual row integral
almost everywhere. The double integrals and row integrals are proved integrable. -/
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace Resonance.L2KernelReadout
noncomputable section
open Resonance.L2KernelPairing
variable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ:Measure X) (ν:Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def row (K:Lp ℝ 2 (μ.prod ν)) (u:Lp ℝ 2 ν) (x:X) : ℝ := ∫y,K (x,y)*u y ∂ν

theorem kernel_input_integrable (K:Lp ℝ 2 (μ.prod ν)) (u:Lp ℝ 2 ν) :
    Integrable (fun p:X×Y=>K p*u p.2) (μ.prod ν) :=
  (Lp.memLp K).integrable_mul ((Lp.memLp u).comp_snd μ)

theorem row_integrable (K:Lp ℝ 2 (μ.prod ν)) (u:Lp ℝ 2 ν) : Integrable (row μ ν K u) μ :=
  (kernel_input_integrable μ ν K u).integral_prod_left

theorem row_integrable_ae (K:Lp ℝ 2 (μ.prod ν)) (u:Lp ℝ 2 ν) :
    ∀ᵐx∂μ,Integrable (fun y=>K (x,y)*u y) ν :=
  (kernel_input_integrable μ ν K u).prod_right_ae

theorem represents_row_ae {K:Lp ℝ 2 (μ.prod ν)} {T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ}
    (hT:Represents μ ν K T) (u:Lp ℝ 2 ν) : T u=ᵐ[μ]row μ ν K u := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp (T u)).integrable (by norm_num)) (row_integrable μ ν K u)
  intro s hs _
  let v : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top _ _) (1:ℝ)
  have hv : v=ᵐ[μ]s.indicator (fun _=>(1:ℝ)) := indicatorConstLp_coeFn
  calc
    (∫x in s,T u x ∂μ)=inner ℝ v (T u) := by
      rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
      congr 1
      ext x
      change T u x=T u x*1
      ring
    _ = ∫p,K p*u p.2*v p.1 ∂(μ.prod ν) := hT u v
    _ = ∫x,row μ ν K u x*v x ∂μ := by
      rw [integral_prod _ (pairing_integrable μ ν K u v)]
      simp only [row,integral_mul_const]
    _ = ∫x in s,row μ ν K u x ∂μ := by
      rw [←integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
      by_cases hxs:x∈s <;> simp [hxs]

theorem represented_row_memLp {K:Lp ℝ 2 (μ.prod ν)} {T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ}
    (hT:Represents μ ν K T) (u:Lp ℝ 2 ν) : MemLp (row μ ν K u) 2 μ :=
  (Lp.memLp (T u)).ae_eq (represents_row_ae μ ν hT u)

end
end Resonance.L2KernelReadout
