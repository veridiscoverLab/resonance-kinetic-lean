import Resonance.PinnedVelocityLevels
import Resonance.PinnedMeasure

/-! Critical geometry of the actual pinned square-root energy surface.
The critical classification below is derived from the velocity quadratic;
no finite-branch or critical-set classification is supplied as an assumption. -/
open Real Set
open scoped ContDiff
namespace Resonance.PinnedCriticalGeometry
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure

theorem quadratic_third_root {A B C a b c : ℝ} (hA : A ≠ 0) (hab : a ≠ b)
    (ha : A*a^2+B*a+C=0) (hb : A*b^2+B*b+C=0)
    (hc : A*c^2+B*c+C=0) : c=a ∨ c=b := by
  have hs : A*(a+b)+B=0 := by
    have hz : (a-b)*(A*(a+b)+B)=0 := by linear_combination ha-hb
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)
  have hz : A*((c-a)*(c-b))=0 := by
    linear_combination hc-ha-(c-a)*hs
  have ht := (mul_eq_zero.mp hz).resolve_left hA
  simpa only [sub_eq_zero] using mul_eq_zero.mp ht

theorem omega_eq_iff_cos_eq {d x y : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    omega d x=omega d y ↔ cos x=cos y := by
  constructor
  · intro he
    have hdL : -(1/2:ℝ)<d := by linarith
    have hs := congrArg (fun t : ℝ => t^2) he
    dsimp at hs
    rw [omega_sq hdL hdU,omega_sq hdL hdU] at hs
    nlinarith
  · intro he
    simp only [omega,Collision.pinnedDispersion,he]

theorem same_velocity_same_cos_sin {d x y : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (hv : velocity d x=velocity d y) (hc : cos x=cos y) : sin x=sin y := by
  have hw := (omega_eq_iff_cos_eq hd0 hdU).mpr hc
  have hdL : -(1/2:ℝ)<d := by linarith
  have hn := ne_of_gt (signed_omega_pos hdL hdU y)
  change d*sin x/omega d x=d*sin y/omega d y at hv
  rw [hw] at hv
  have hm := (div_left_inj' hn).mp hv
  exact mul_left_cancel₀ hd0.ne' hm

theorem velocity_level_two_cosines {d x y z : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (hxy : velocity d x=velocity d y) (hxz : velocity d x=velocity d z)
    (hcos : cos x≠cos y) : cos z=cos x ∨ cos z=cos y := by
  apply quadratic_third_root (B := -2*(velocity d x)^2*d)
    (C := (velocity d x)^2-d^2) (pow_ne_zero 2 hd0.ne') hcos
  · simpa only [neg_mul,sub_eq_add_neg] using
      PinnedVelocityLevels.velocity_level_quadratic hd0 hdU (rfl : velocity d x=velocity d x)
  · simpa only [neg_mul,sub_eq_add_neg] using
      PinnedVelocityLevels.velocity_level_quadratic hd0 hdU hxy.symm
  · simpa only [neg_mul,sub_eq_add_neg] using
      PinnedVelocityLevels.velocity_level_quadratic hd0 hdU hxz.symm

/-- Energy and common velocity force the two incoming values of omega to be
the two outgoing values, with their multiplicities, not just their set. -/
theorem critical_omega_pairing {d x y z w : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (hx : velocity d x=velocity d z) (hy : velocity d y=velocity d z)
    (hw : velocity d w=velocity d z)
    (he : omega d x+omega d y=omega d z+omega d w) :
    (omega d x=omega d z ∧ omega d y=omega d w) ∨
    (omega d x=omega d w ∧ omega d y=omega d z) := by
  by_cases hzw : cos z=cos w
  · have hωzw := (omega_eq_iff_cos_eq hd0 hdU).mpr hzw
    by_cases hxz : cos x=cos z
    · have hωxz := (omega_eq_iff_cos_eq hd0 hdU).mpr hxz
      exact Or.inl ⟨hωxz,by linarith⟩
    · have hcy := velocity_level_two_cosines hd0 hdU hx (hx.trans hy.symm) hxz
      rcases hcy with hcy | hcy
      · have hωyx := (omega_eq_iff_cos_eq hd0 hdU).mpr hcy
        have hωxz : omega d x=omega d z := by linarith
        exact (hxz ((omega_eq_iff_cos_eq hd0 hdU).mp hωxz)).elim
      · have hωyz := (omega_eq_iff_cos_eq hd0 hdU).mpr hcy
        have hωxz : omega d x=omega d z := by linarith
        exact (hxz ((omega_eq_iff_cos_eq hd0 hdU).mp hωxz)).elim
  · have hcx := velocity_level_two_cosines hd0 hdU hw.symm hx.symm hzw
    have hcy := velocity_level_two_cosines hd0 hdU hw.symm hy.symm hzw
    rcases hcx with hcx | hcx <;> rcases hcy with hcy | hcy
    · have hωxz := (omega_eq_iff_cos_eq hd0 hdU).mpr hcx
      have hωyz := (omega_eq_iff_cos_eq hd0 hdU).mpr hcy
      have hωzw : omega d z=omega d w := by linarith
      exact (hzw ((omega_eq_iff_cos_eq hd0 hdU).mp hωzw)).elim
    · exact Or.inl ⟨(omega_eq_iff_cos_eq hd0 hdU).mpr hcx,
        (omega_eq_iff_cos_eq hd0 hdU).mpr hcy⟩
    · exact Or.inr ⟨(omega_eq_iff_cos_eq hd0 hdU).mpr hcx,
        (omega_eq_iff_cos_eq hd0 hdU).mpr hcy⟩
    · have hωxw := (omega_eq_iff_cos_eq hd0 hdU).mpr hcx
      have hωyw := (omega_eq_iff_cos_eq hd0 hdU).mpr hcy
      have hωzw : omega d z=omega d w := by linarith
      exact (hzw ((omega_eq_iff_cos_eq hd0 hdU).mp hωzw)).elim

/-- Every critical quartet is a trivial permutation on the circle, expressed
without choosing a discontinuous angular representative. -/
theorem critical_trigonometric_pairing {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ((cos (k 0)=cos (k 2) ∧ sin (k 0)=sin (k 2)) ∧
      (cos (k 1)=cos (k 0+k 1-k 2) ∧ sin (k 1)=sin (k 0+k 1-k 2))) ∨
    ((cos (k 0)=cos (k 0+k 1-k 2) ∧ sin (k 0)=sin (k 0+k 1-k 2)) ∧
      (cos (k 1)=cos (k 2) ∧ sin (k 1)=sin (k 2))) := by
  have h0 := congrArg (fun p : Ambient => p 0) hg
  have h1 := congrArg (fun p : Ambient => p 1) hg
  have h2 := congrArg (fun p : Ambient => p 2) hg
  change velocity d (k 0)-velocity d (k 0+k 1-k 2)=0 at h0
  change velocity d (k 1)-velocity d (k 0+k 1-k 2)=0 at h1
  change velocity d (k 0+k 1-k 2)-velocity d (k 2)=0 at h2
  have hv0 := (sub_eq_zero.mp h0).trans (sub_eq_zero.mp h2)
  have hv1 := (sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2)
  have hv2 := sub_eq_zero.mp h2
  have hv0w := sub_eq_zero.mp h0
  have hv1w := sub_eq_zero.mp h1
  have he' : omega d (k 0)+omega d (k 1)=omega d (k 2)+omega d (k 0+k 1-k 2) := by
    change omega d (k 0)+omega d (k 1)-omega d (k 2)-omega d (k 0+k 1-k 2)=0 at he
    linarith
  have hp := critical_omega_pairing hd0 hdU hv0 hv1 hv2 he'
  have ht : ∀ a b, velocity d a=velocity d b → omega d a=omega d b →
      cos a=cos b ∧ sin a=sin b := by
    intro a b hv hω
    have hc := (omega_eq_iff_cos_eq hd0 hdU).mp hω
    exact ⟨hc,same_velocity_same_cos_sin hd0 hdU hv hc⟩
  rcases hp with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact Or.inl ⟨ht _ _ hv0 h0,ht _ _ hv1w h1⟩
  · exact Or.inr ⟨ht _ _ hv0w h0,ht _ _ hv1 h1⟩

theorem trigonometric_pair_integer_shift {x y : ℝ}
    (hc : cos x=cos y) (hs : sin x=sin y) :
    ∃ n : ℤ, x=y+(n:ℝ)*(2*Real.pi) := by
  have h : cos (x-y)=1 := by
    rw [Real.cos_sub,hc,hs]
    nlinarith [Real.sin_sq_add_cos_sq y]
  obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff (x-y)).mp h
  exact ⟨n,by linarith⟩

/-- The lifted critical set is the union of the two genuine periodic trivial
pairings. This statement includes Umklapp, without deleting a branch. -/
theorem critical_integer_pairing {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    (∃ n : ℤ, k 0=k 2+(n:ℝ)*(2*Real.pi)) ∨
    (∃ n : ℤ, k 1=k 2+(n:ℝ)*(2*Real.pi)) := by
  rcases critical_trigonometric_pairing hd0 hdU he hg with h | h
  · exact Or.inl (trigonometric_pair_integer_shift h.1.1 h.1.2)
  · exact Or.inr (trigonometric_pair_integer_shift h.2.1 h.2.2)

theorem velocity_curvature_formula {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (x : ℝ) :
    deriv (velocity d) x=d*(cos x-d*(1+(cos x)^2))/(omega d x)^3 := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hw := ne_of_gt (signed_omega_pos hdL hdU x)
  rw [PinnedClassification.velocity_deriv_formula hd0 hdU]
  field_simp
  linear_combination cos x*(omega_sq hdL hdU x)-d*(Real.sin_sq_add_cos_sq x)

/-- At two distinct cosine values with the same velocity the two curvatures
have opposite signs. The displayed exact identity gives their nondegeneracy. -/
theorem equal_velocity_curvature_identity {d x y : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hv : velocity d x=velocity d y)
    (hc : cos x≠cos y) :
    deriv (velocity d) x=d*(cos x-cos y)/(2*omega d x) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hw := ne_of_gt (signed_omega_pos hdL hdU x)
  have hx := PinnedVelocityLevels.velocity_level_quadratic hd0 hdU
    (rfl : velocity d x=velocity d x)
  have hy := PinnedVelocityLevels.velocity_level_quadratic hd0 hdU hv.symm
  have hs : d*(cos x+cos y)-2*(velocity d x)^2=0 := by
    have hz : d*(cos x-cos y)*(d*(cos x+cos y)-2*(velocity d x)^2)=0 := by
      linear_combination hx-hy
    exact (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero hd0.ne' (sub_ne_zero.mpr hc))
  have hp : 2*(cos x-d*(1+(cos x)^2))=
      (1-2*d*cos x)*(cos x-cos y) := by
    have hz : d*(2*(cos x-d*(1+(cos x)^2))-
        (1-2*d*cos x)*(cos x-cos y))=0 := by
      linear_combination 2*hx+(1-2*d*cos x)*hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hd0.ne')
  rw [velocity_curvature_formula hd0 hdU]
  field_simp
  nlinarith [omega_sq hdL hdU x]

theorem equal_velocity_curvature_product_neg {d x y : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hv : velocity d x=velocity d y)
    (hc : cos x≠cos y) :
    deriv (velocity d) x*deriv (velocity d) y<0 := by
  have hdL : -(1/2:ℝ)<d := by linarith
  rw [equal_velocity_curvature_identity hd0 hdU hv hc,
    equal_velocity_curvature_identity hd0 hdU hv.symm hc.symm]
  have hx := signed_omega_pos hdL hdU x
  have hy := signed_omega_pos hdL hdU y
  have hs : (cos x-cos y)^2>0 := sq_pos_of_ne_zero (sub_ne_zero.mpr hc)
  have he : (d*(cos x-cos y)/(2*omega d x))*(d*(cos y-cos x)/(2*omega d y))=
      -(d^2*(cos x-cos y)^2)/(4*omega d x*omega d y) := by ring
  rw [he]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (sq_pos_of_pos hd0) hs))
    (by positivity)

theorem equal_velocity_curvatures_ne {d x y : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hv : velocity d x=velocity d y)
    (hc : cos x≠cos y) : deriv (velocity d) x≠deriv (velocity d) y := by
  have hn := equal_velocity_curvature_product_neg hd0 hdU hv hc
  intro he
  rw [he] at hn
  nlinarith [sq_nonneg (deriv (velocity d) y)]

theorem critical_curvature_sine_ne_zero {d x : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hc : deriv (velocity d) x=0) : sin x≠0 := by
  have hq := PinnedVelocityLevels.velocity_critical_quadratic hd0 hdU hc
  intro hs
  have ht := Real.sin_sq_add_cos_sq x
  rw [hs] at ht
  have hcos : cos x=1 ∨ cos x= -1 := by
    have hz : (cos x-1)*(cos x+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hcos with hcos | hcos <;> rw [hcos] at hq <;> nlinarith

/-- An inflection of omega is simple. At that point the next derivative is
exactly minus the actual velocity, so no endpoint or repeated critical root
is silently discarded. -/
theorem curvature_hasDerivAt_at_zero {d x : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hc : deriv (velocity d) x=0) :
    HasDerivAt (deriv (velocity d)) (-velocity d x) x := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hw := ne_of_gt (signed_omega_pos hdL hdU x)
  have hq := PinnedVelocityLevels.velocity_critical_quadratic hd0 hdU hc
  have hn : d*(cos x-d*(1+(cos x)^2))=0 := by nlinarith
  have hp := ((hasDerivAt_cos x).sub
    ((((hasDerivAt_cos x).pow 2).const_add 1).const_mul d)).const_mul d
  have hr := hp.div ((omega_hasDerivAt hdL hdU x).pow 3) (pow_ne_zero 3 hw)
  have he : deriv (velocity d)=fun t => d*(cos t-d*(1+(cos t)^2))/(omega d t)^3 :=
    funext (velocity_curvature_formula hd0 hdU)
  rw [he]
  convert hr using 1
  dsimp
  rw [hn]
  simp only [zero_mul,sub_zero]
  unfold velocity
  field_simp
  linear_combination -(sin x)*(omega_sq hdL hdU x)

theorem simple_inflection {d x : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hc : deriv (velocity d) x=0) :
    deriv (deriv (velocity d)) x≠0 := by
  rw [(curvature_hasDerivAt_at_zero hd0 hdU hc).deriv]
  have hdL : -(1/2:ℝ)<d := by linarith
  exact neg_ne_zero.mpr (div_ne_zero
    (mul_ne_zero hd0.ne' (critical_curvature_sine_ne_zero hd0 hdU hc))
    (ne_of_gt (signed_omega_pos hdL hdU x)))

end
end Resonance.PinnedCriticalGeometry
