import Resonance.UniformHilbertCompensation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Actual ODE energy differentiation and integration of the exponential
factor. No exponential stability premise is used. -/
open ContinuousLinearMap InnerProductSpace Set
namespace Resonance.HilbertODEEnergy
noncomputable section
open HilbertQuadraticBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem hasDerivAt_quadratic (H G : E→L[ℂ]E) {u : ℝ→E} {t : ℝ}
    (hu : HasDerivAt u (G (u t)) t) :
    HasDerivAt (fun s=>quadratic H (u s))
      (quadratic (H*G+star G*H) (u t)) t := by
  have hH := (H.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hi := hu.inner ℂ hH
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hi
  convert hr using 1
  change (inner ℂ (u t) (H (G (u t))+star G (H (u t)))).re=
    (inner ℂ (u t) (H (G (u t)))+inner ℂ (G (u t)) (H (u t))).re
  have he : inner ℂ (u t) (star G (H (u t)))=inner ℂ (G (u t)) (H (u t)) :=
    G.adjoint_inner_right _ _
  rw [inner_add_right,he]

theorem scalar_exponential_decay {y y' : ℝ→ℝ} (hy : ∀t,HasDerivAt y (y' t) t)
    (a : ℝ) (hb : ∀t,y' t≤-a*y t) {t : ℝ} (ht : 0≤t) :
    y t≤Real.exp (-a*t)*y 0 := by
  let F := fun s=>Real.exp (a*s)*y s
  have hF : ∀s,HasDerivAt F (Real.exp (a*s)*(a*y s+y' s)) s := by
    intro s
    convert ((((hasDerivAt_id s).const_mul a).exp).mul (hy s)) using 1
    dsimp [F]
    ring
  have hanti : Antitone F := antitone_of_hasDerivAt_nonpos hF (fun s=>by
    have hh : a*y s+y' s≤0 := by linarith [hb s]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hh)
  have hbound : Real.exp (a*t)*y t≤y 0 := by simpa only [F,mul_zero,Real.exp_zero,one_mul] using hanti ht
  calc
    y t=Real.exp (-a*t)*(Real.exp (a*t)*y t) := by
      rw [←mul_assoc,←Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

theorem quadratic_ODE_decay (H G : E→L[ℂ]E) {δ : ℝ} (hδ : 0≤δ)
    (hlo : ∀v:E,(1/2:ℝ)*‖v‖^2≤quadratic H v)
    (hhi : ∀v:E,quadratic H v≤(3/2:ℝ)*‖v‖^2)
    (hD : ∀v:E,quadratic (H*G+star G*H) v≤-δ*‖v‖^2)
    {u : ℝ→E} (hu : ∀s,HasDerivAt u (G (u s)) s) {t : ℝ} (ht : 0≤t) :
    ‖u t‖^2≤3*Real.exp (-(2*δ/3)*t)*‖u 0‖^2 := by
  have hb : ∀s,quadratic (H*G+star G*H) (u s)≤-(2*δ/3)*quadratic H (u s) := by
    intro s
    have hh := mul_le_mul_of_nonneg_left (hhi (u s)) (show 0≤2*δ/3 by positivity)
    nlinarith [hD (u s)]
  have hy := scalar_exponential_decay (fun s=>hasDerivAt_quadratic H G (hu s)) (2*δ/3) hb ht
  have h0 := mul_le_mul_of_nonneg_left (hhi (u 0)) (Real.exp_pos (-(2*δ/3)*t)).le
  nlinarith [hlo (u t)]

end
end Resonance.HilbertODEEnergy
