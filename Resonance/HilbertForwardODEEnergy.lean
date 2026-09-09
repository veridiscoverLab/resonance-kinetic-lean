import Resonance.HilbertODEEnergy

/-! Energy integration on a forward closed time interval only. Neither a
negative-time extension nor a solution outside the displayed interval occurs
among the hypotheses. -/
open ContinuousLinearMap InnerProductSpace Set
namespace Resonance.HilbertForwardODEEnergy
noncomputable section
open HilbertQuadraticBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem hasDerivWithinAt_quadratic (H G : E→L[ℂ]E) {u : ℝ→E} {t : ℝ} {S : Set ℝ}
    (hu : HasDerivWithinAt u (G (u t)) S t) :
    HasDerivWithinAt (fun s=>quadratic H (u s))
      (quadratic (H*G+star G*H) (u t)) S t := by
  have hH := (H.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hu
  have hi := hu.inner ℂ hH
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hi
  convert hr using 1
  change (inner ℂ (u t) (H (G (u t))+star G (H (u t)))).re=
    (inner ℂ (u t) (H (G (u t)))+inner ℂ (G (u t)) (H (u t))).re
  have he : inner ℂ (u t) (star G (H (u t)))=inner ℂ (G (u t)) (H (u t)) :=
    G.adjoint_inner_right _ _
  rw [inner_add_right,he]

theorem scalar_forward_decay {y y' : ℝ→ℝ} {T : ℝ} (hT : 0≤T)
    (hy : ∀s∈Icc 0 T,HasDerivWithinAt y (y' s) (Icc 0 T) s)
    (a : ℝ) (hb : ∀s∈Icc 0 T,y' s≤-a*y s) :
    y T≤Real.exp (-a*T)*y 0 := by
  let F := fun s=>Real.exp (a*s)*y s
  let F' := fun s=>Real.exp (a*s)*(a*y s+y' s)
  have hF : ∀s∈Icc 0 T,HasDerivWithinAt F (F' s) (Icc 0 T) s := by
    intro s hs
    convert (((((hasDerivAt_id s).const_mul a).exp).hasDerivWithinAt).mul (hy s hs)) using 1
    dsimp [F,F']
    ring
  have hanti : AntitoneOn F (Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (fun s hs=>(hF s hs).continuousWithinAt)
      (fun s hs=>(hF s (interior_subset hs)).mono interior_subset)
      (fun s hs=>by
        have hh : a*y s+y' s≤0 := by linarith [hb s (interior_subset hs)]
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hh)
  have hbound : Real.exp (a*T)*y T≤y 0 := by
    simpa only [F,mul_zero,Real.exp_zero,one_mul] using
      hanti ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT
  calc
    y T=Real.exp (-a*T)*(Real.exp (a*T)*y T) := by
      rw [←mul_assoc,←Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

theorem quadratic_forward_decay (H G : E→L[ℂ]E) {δ : ℝ} (hδ : 0≤δ)
    (hlo : ∀v:E,(1/2:ℝ)*‖v‖^2≤quadratic H v)
    (hhi : ∀v:E,quadratic H v≤(3/2:ℝ)*‖v‖^2)
    (hD : ∀v:E,quadratic (H*G+star G*H) v≤-δ*‖v‖^2)
    {u : ℝ→E} {T : ℝ} (hT : 0≤T)
    (hu : ∀s∈Icc 0 T,HasDerivWithinAt u (G (u s)) (Icc 0 T) s) :
    ‖u T‖^2≤3*Real.exp (-(2*δ/3)*T)*‖u 0‖^2 := by
  have hb : ∀s∈Icc 0 T,quadratic (H*G+star G*H) (u s)≤-(2*δ/3)*quadratic H (u s) := by
    intro s _
    have hh := mul_le_mul_of_nonneg_left (hhi (u s)) (show 0≤2*δ/3 by positivity)
    nlinarith [hD (u s)]
  have hy := scalar_forward_decay hT (fun s hs=>hasDerivWithinAt_quadratic H G (hu s hs))
    (2*δ/3) hb
  have h0 := mul_le_mul_of_nonneg_left (hhi (u 0)) (Real.exp_pos (-(2*δ/3)*T)).le
  nlinarith [hlo (u T)]

end
end Resonance.HilbertForwardODEEnergy
