import Resonance.PinnedClassification
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! Countability of every actual pinned velocity level and of its critical
points.  Both facts are derived from the exact sqrt dispersion and explicit
nonzero quadratic polynomials in cos x; no monotonicity decomposition or
analytic-null-set hypothesis is assumed. -/
open Real Set Polynomial
namespace Resonance.PinnedVelocityLevels
noncomputable section
open Resonance.PinnedGeometry

theorem cosine_level_countable (t : ℝ) : {x : ℝ | cos x = t}.Countable := by
  by_cases h : ∃ y : ℝ, cos y = t
  · obtain ⟨y,hy⟩ := h
    have hc := (countable_range (fun k : ℤ => 2*(k:ℝ)*Real.pi+y)).union
      (countable_range (fun k : ℤ => 2*(k:ℝ)*Real.pi-y))
    apply hc.mono
    intro x hx
    obtain ⟨k,hk|hk⟩ := Real.cos_eq_cos_iff.mp (hy.trans hx.symm)
    · exact Or.inl ⟨k,hk.symm⟩
    · exact Or.inr ⟨k,hk.symm⟩
  · have he : {x : ℝ | cos x = t} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun hx => h ⟨x,hx⟩
    rw [he]
    exact countable_empty

theorem cosine_preimage_countable {s : Set ℝ} (hs : s.Countable) :
    (Real.cos ⁻¹' s).Countable := by
  have hc := hs.biUnion (fun t _ => cosine_level_countable t)
  apply hc.mono
  intro x hx
  exact mem_iUnion.mpr ⟨cos x, mem_iUnion.mpr ⟨hx, rfl⟩⟩

theorem quadratic_cosine_zero_countable (a b c : ℝ) (ha : a ≠ 0) :
    {x : ℝ | a*(cos x)^2+b*cos x+c=0}.Countable := by
  let p : Polynomial ℝ := C a*X^2+C b*X+C c
  have hp : p ≠ 0 := by
    intro h
    have he := congrArg (fun q : Polynomial ℝ => q.coeff 2) h
    simp [p, coeff_C_mul, coeff_X_pow] at he
    exact ha he
  have hc := cosine_preimage_countable (finite_setOf_isRoot hp).countable
  apply hc.mono
  intro x hx
  change p.IsRoot (cos x)
  simpa [p, Polynomial.IsRoot] using hx

theorem velocity_level_quadratic {d v x : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (hx : velocity d x = v) :
    d^2*(cos x)^2-2*v^2*d*cos x+(v^2-d^2)=0 := by
  have hdL : -(1/2:ℝ) < d := by linarith
  have hw := ne_of_gt (signed_omega_pos hdL hdU x)
  have hm : d*sin x=v*omega d x := (div_eq_iff hw).mp hx
  have hsq := congrArg (fun t : ℝ => t^2) hm
  simp only [mul_pow, omega_sq hdL hdU x] at hsq
  linear_combination d^2*(Real.sin_sq_add_cos_sq x)-hsq

theorem velocity_level_countable {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) (v : ℝ) :
    {x : ℝ | velocity d x=v}.Countable := by
  have hc := quadratic_cosine_zero_countable (d^2) (-2*v^2*d) (v^2-d^2)
    (pow_ne_zero 2 hd0.ne')
  apply hc.mono
  intro x hx
  have h := velocity_level_quadratic hd0 hdU hx
  simpa only [neg_mul, sub_eq_add_neg] using h

theorem velocity_critical_quadratic {d x : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (hx : deriv (velocity d) x=0) : d*(cos x)^2-cos x+d=0 := by
  have hdL : -(1/2:ℝ) < d := by linarith
  have hw := ne_of_gt (signed_omega_pos hdL hdU x)
  rw [PinnedClassification.velocity_deriv_formula hd0 hdU] at hx
  have hm : d*cos x*(omega d x)^2-d^2*(sin x)^2=0 := by
    calc
      _ = (d*cos x/omega d x-d^2*(sin x)^2/(omega d x)^3)*(omega d x)^3 := by
        field_simp
      _ = 0 := by rw [hx]; ring
  rw [omega_sq hdL hdU x] at hm
  have he : d*(d*(cos x)^2-cos x+d)=0 := by
    linear_combination -hm-d^2*(Real.sin_sq_add_cos_sq x)
  exact (mul_eq_zero.mp he).resolve_left hd0.ne'

theorem velocity_critical_countable {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) :
    {x : ℝ | deriv (velocity d) x=0}.Countable := by
  have hc := quadratic_cosine_zero_countable d (-1) d hd0.ne'
  apply hc.mono
  intro x hx
  have h := velocity_critical_quadratic hd0 hdU hx
  simpa only [neg_one_mul, sub_eq_add_neg] using h

end
end Resonance.PinnedVelocityLevels
