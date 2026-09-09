import Resonance.FixedMultiplier

/-! Actual almost-everywhere L² slices of a product-space vector, with the
full squared-norm Fubini identity. The zero used on exceptional non-L² slices
has no effect: membership and equality are proved outside one null set. -/
open MeasureTheory MeasureTheory.Measure
namespace Resonance.ProductL2Slices
noncomputable section
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]

theorem slice_memLp_ae (u : Lp ℝ 2 (μ.prod ν)) :
    ∀ᵐa∂μ,MemLp (fun b=>u (a,b)) 2 ν := by
  have hi:=(Lp.memLp u).integrable_norm_pow (by norm_num)
  filter_upwards [(Lp.memLp u).aestronglyMeasurable.prodMk_left,hi.prod_right_ae]
    with a hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

def slice (u : Lp ℝ 2 (μ.prod ν)) (a : A) : Lp ℝ 2 ν := by
  classical
  exact if h:MemLp (fun b=>u (a,b)) 2 ν then h.toLp (fun b=>u (a,b)) else 0

theorem slice_ae (u : Lp ℝ 2 (μ.prod ν)) :
    ∀ᵐa∂μ,(slice u a: B→ℝ)=ᵐ[ν](fun b=>u (a,b)) := by
  filter_upwards [slice_memLp_ae u] with a ha
  simp only [slice,dif_pos ha]
  exact MemLp.coeFn_toLp _

theorem slice_square_ae (u : Lp ℝ 2 (μ.prod ν)) :
    (fun a=>‖slice u a‖^2)=ᵐ[μ](fun a=>∫b,‖u (a,b)‖^2∂ν) := by
  filter_upwards [slice_memLp_ae u] with a ha
  simp only [slice,dif_pos ha]
  rw [FixedMultiplier.L2_norm_eq_sqrt ha,Real.sq_sqrt]
  exact integral_nonneg (fun b=>sq_nonneg _)

theorem slice_square_integrable (u : Lp ℝ 2 (μ.prod ν)) :
    Integrable (fun a=>‖slice u a‖^2) μ := by
  have hi:=(Lp.memLp u).integrable_norm_pow (by norm_num)
  exact hi.integral_prod_left.congr (slice_square_ae u).symm

theorem norm_square_integral (u : Lp ℝ 2 (μ.prod ν)) :
    ‖u‖^2=∫a,‖slice u a‖^2∂μ := by
  have hi:=(Lp.memLp u).integrable_norm_pow (by norm_num)
  calc
    ‖u‖^2=∫p,‖u p‖^2∂μ.prod ν := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      exact ae_of_all _ (fun p=>real_inner_self_eq_norm_sq (u p))
    _=∫a,∫b,‖u (a,b)‖^2∂ν∂μ:=integral_prod _ hi
    _=∫a,‖slice u a‖^2∂μ:=integral_congr_ae (slice_square_ae u).symm

theorem slice_sub_ae (u v : Lp ℝ 2 (μ.prod ν)) :
    ∀ᵐa∂μ,slice (u-v) a=slice u a-slice v a := by
  filter_upwards [slice_ae (u-v),slice_ae u,slice_ae v,
    ae_ae_of_ae_prod (Lp.coeFn_sub u v)] with a huv hu hv hsub
  apply Lp.ext
  filter_upwards [huv,hu,hv,hsub,Lp.coeFn_sub (slice u a) (slice v a)]
    with b huv hu hv hsub hout
  simp only [Pi.sub_apply] at hsub hout
  rw [huv,hout,hu,hv,hsub]

end
end Resonance.ProductL2Slices
