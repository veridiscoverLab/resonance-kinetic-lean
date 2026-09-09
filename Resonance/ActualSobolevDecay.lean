import Resonance.ActualSobolevSemigroup

/-! The ordinary norm estimate in the paper, uniform on compact positive
parameter sets, with all five zero-mode constraints and the original c≥1 clock. -/
open Set
open scoped NNReal
namespace Resonance.ActualSobolevDecay
noncomputable section
open Thermodynamics ActualSobolevSpace ActualSobolevSemigroup

theorem norm_bound_of_square {x y a : ℝ} (hx : 0≤x) (hy : 0≤y)
    (h : x^2≤3*Real.exp a*y^2) : x≤Real.sqrt 3*Real.exp (a/2)*y := by
  apply (sq_le_sq₀ hx (by positivity)).mp
  have he : (Real.sqrt 3*Real.exp (a/2)*y)^2=3*Real.exp a*y^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),
      pow_two (Real.exp (a/2)),←Real.exp_add]
    rw [show a/2+a/2=a by ring]
  rw [he]
  exact h

theorem lattice_clock_lower {c : ℝ} (hc : 1≤c) : 1/(2*c)≤c/(c^2+1) := by
  have hp : 0<c := lt_of_lt_of_le zero_lt_one hc
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hs : 1≤c^2 := by nlinarith
  nlinarith

theorem original_torus_sobolev_decay {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃a : ℝ,0<a ∧ ∀θ : K,∀c : ℝ,∀hc : 1≤c,∀s : ℝ,∀t : ℝ≥0,
      ∀v : Sobolev s,coefficient hR (hpos θ.property) s v 0=0 →
      ‖evolution hR (hpos θ.property) (lt_of_lt_of_le zero_lt_one hc) s t v‖≤
        Real.sqrt 3*Real.exp (-a*t/c)*‖v‖ := by
  obtain ⟨δ,hδ,hd⟩ := sobolev_mean_zero_decay hR hK hpos
  refine ⟨δ/4,by positivity,?_⟩
  intro θ c hc s t v hv
  have hp : 0<c := lt_of_lt_of_le zero_lt_one hc
  have hb := hd θ c hp s t v hv
  have he : Real.exp (-δ*(c/(c^2+1))*t)≤Real.exp (-δ*(1/(2*c))*t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonpos_left (lattice_clock_lower hc) (neg_nonpos.mpr hδ.le)) t.property)
  have hh : ‖evolution hR (hpos θ.property) hp s t v‖^2≤
      3*Real.exp (-δ*(1/(2*c))*t)*‖v‖^2 :=
    hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (by norm_num)) (sq_nonneg _))
  have hn := norm_bound_of_square (norm_nonneg _) (norm_nonneg _) hh
  have heq : -δ*(1/(2*c))*(t:ℝ)/2=-(δ/4)*t/c := by ring
  rwa [heq] at hn

end
end Resonance.ActualSobolevDecay
