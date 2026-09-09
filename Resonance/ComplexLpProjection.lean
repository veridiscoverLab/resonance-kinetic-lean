import Resonance.ComplexLpLinear

/-! Orthogonal projection commutes with actual L2 complexification,
proved through all four real-imaginary inner products. -/
open MeasureTheory
namespace Resonance.ComplexLpProjection
noncomputable section
open ComplexLpDecomposition ComplexLpLinear

theorem inner_parts_re {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : Lp ℂ 2 μ) : (inner ℂ u v).re=
      inner ℝ (realPart μ u) (realPart μ v)+inner ℝ (imagPart μ u) (imagPart μ v) := by
  change RCLike.re (inner ℂ u v)=_
  rw [L2.inner_def,←integral_re (L2.integrable_inner (𝕜:=ℂ) u v),L2.inner_def,L2.inner_def,
    ←integral_add (L2.integrable_inner (𝕜:=ℝ) (realPart μ u) (realPart μ v))
      (L2.integrable_inner (𝕜:=ℝ) (imagPart μ u) (imagPart μ v))]
  apply integral_congr_ae
  filter_upwards [realPart_ae u,realPart_ae v,imagPart_ae u,imagPart_ae v] with x hu hv hi hj
  change (v x*star (u x)).re=realPart μ v x*realPart μ u x+imagPart μ v x*imagPart μ u x
  rw [hu,hv,hi,hj]
  simp

theorem inner_parts_im {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : Lp ℂ 2 μ) : (inner ℂ u v).im=
      inner ℝ (realPart μ u) (imagPart μ v)-inner ℝ (imagPart μ u) (realPart μ v) := by
  change RCLike.im (inner ℂ u v)=_
  rw [L2.inner_def,←integral_im (L2.integrable_inner (𝕜:=ℂ) u v),L2.inner_def,L2.inner_def,
    ←integral_sub (L2.integrable_inner (𝕜:=ℝ) (realPart μ u) (imagPart μ v))
      (L2.integrable_inner (𝕜:=ℝ) (imagPart μ u) (realPart μ v))]
  apply integral_congr_ae
  filter_upwards [realPart_ae u,realPart_ae v,imagPart_ae u,imagPart_ae v] with x hu hv hi hj
  change (v x*star (u x)).im=imagPart μ v x*realPart μ u x-realPart μ v x*imagPart μ u x
  rw [hu,hv,hi,hj]
  simp
  ring

theorem lift_starProjection {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν) (u : Lp ℂ 2 μ) :
    (complexLift T).ker.starProjection u=lift T.ker.starProjection u := by
  apply (complexLift T).ker.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (complexLift_zero_iff T _).mpr
    rw [realPart_lift,imagPart_lift]
    exact ⟨T.ker.starProjection_apply_mem _,T.ker.starProjection_apply_mem _⟩
  · intro w hw
    obtain ⟨hr,hi⟩ := (complexLift_zero_iff T w).mp hw
    apply Complex.ext
    · rw [inner_parts_re,map_sub,map_sub,realPart_lift,imagPart_lift]
      rw [T.ker.starProjection_inner_eq_zero _ _ hr,T.ker.starProjection_inner_eq_zero _ _ hi]
      simp
    · rw [inner_parts_im,map_sub,map_sub,realPart_lift,imagPart_lift]
      rw [T.ker.starProjection_inner_eq_zero _ _ hi,T.ker.starProjection_inner_eq_zero _ _ hr]
      simp

end
end Resonance.ComplexLpProjection
