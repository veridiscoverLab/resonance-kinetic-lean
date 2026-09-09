import Resonance.FourierCompensationWeights

/-! Explicit absorption of both commutator cross terms. The smallness
conditions are algebraic choices of a fixed compensation amplitude. -/
namespace Resonance.CompensationAbsorption
noncomputable section
open FourierCompensationWeights

theorem cross_bound {β d η p z : ℝ} (hβ : 0<β) (hd : 0<d)
    (hsq : z^2≤η*d*p) (M x y : ℝ) :
    2*M*z*x*y≤(β*d/2)*y^2+(2*M^2*η*p/β)*x^2 := by
  have ha : 0<β*d/2 := by positivity
  have hh := weighted_young ha (M*z) y x
  have hc : (M*z)^2/(β*d/2)≤2*M^2*η*p/β := by
    apply (div_le_iff₀ ha).mpr
    have he : (2*M^2*η*p/β)*(β*d/2)=M^2*(η*d*p) := by
      field_simp
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hsq)]
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg x)
  nlinarith

theorem full_absorption {β k d η p q M V x y : ℝ}
    (hβ : 0<β) (hd : 0<d) (hp : 0≤p) (hM : 0≤M)
    (hpp : p^2≤η*d*p) (hqq : q^2≤η*d*p)
    (hpsum : p+q≤2*η*d)
    (hsmall1 : 4*M^2*η≤k*β) (hsmall2 : 4*M*η≤β)
    (hV : V≤-2*β*d*y^2-2*k*p*x^2+
      2*M*p*x*y+M*p*y^2+2*M*q*x*y+M*q*y^2) :
    V≤-k*p*x^2-(β*d/2)*y^2 := by
  have h1 := cross_bound hβ hd hpp M x y
  have h2 := cross_bound hβ hd hqq M x y
  have hco : 4*M^2*η/β≤k := (div_le_iff₀ hβ).mpr hsmall1
  have hmac := mul_le_mul_of_nonneg_right hco (mul_nonneg hp (sq_nonneg x))
  have hsum := mul_le_mul_of_nonneg_left hpsum hM
  have hsmall := mul_le_mul_of_nonneg_right hsmall2 hd.le
  have hy := mul_le_mul_of_nonneg_right (show M*(p+q)≤β*d/2 by nlinarith) (sq_nonneg y)
  have he : (2*M^2*η*p/β)*x^2+(2*M^2*η*p/β)*x^2=
      (4*M^2*η/β)*(p*x^2) := by ring
  nlinarith

end
end Resonance.CompensationAbsorption
