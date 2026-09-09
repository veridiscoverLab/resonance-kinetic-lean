import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Compact

/-! Finite-projection stability of a coercive identity-plus-compact form.
Only a finite-dimensional part of the varying diagonal must be close to
identity; the diagonal may remain order one on its orthogonal complement.
The actual collision diagonal hypotheses are instantiated separately. -/
open Set
open scoped InnerProductSpace
namespace Resonance.ProjectionFormStability
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 1800000

theorem orthogonal_sum_norm (x y : E) (hxy : inner ℝ x y=0) :
    ‖x+y‖^2=‖x‖^2+‖y‖^2 := by
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hxy

theorem vector_form_stability (A K : E→L[ℝ]E) {a c d : ℝ}
    (hd : 0<d) (hda : d≤a) (hdc : d≤c)
    (hA : ∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hlower : ∀x,a*‖x‖^2 ≤ inner ℝ x (A x))
    (hbase : ∀x,c*‖x‖^2≤‖x‖^2+inner ℝ x (K x))
    (x y : E) (hxy : inner ℝ x y=0)
    (hx : ‖A x-x‖≤(d/8)*‖x‖)
    (hK : |inner ℝ (x+y) (K (x+y))-inner ℝ x (K x)|≤(d/8)*‖x+y‖^2) :
    (d/2)*‖x+y‖^2 ≤ inner ℝ (x+y) ((A+K) (x+y)) := by
  have hn:=orthogonal_sum_norm x y hxy
  have hxx : inner ℝ x (A x)≥‖x‖^2-(d/8)*‖x‖^2 := by
    have hb:|inner ℝ x (A x-x)|≤(d/8)*‖x‖^2 := by
      calc
        _≤‖x‖*‖A x-x‖:=abs_real_inner_le_norm _ _
        _≤‖x‖*((d/8)*‖x‖):=mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _=_:=by ring
    rw [inner_sub_right,real_inner_self_eq_norm_sq] at hb
    linarith [(abs_le.mp hb).1]
  have hcross : |inner ℝ x (A y)|≤(d/8)*‖x‖*‖y‖ := by
    rw [←hA x y]
    have he : inner ℝ (A x) y=inner ℝ (A x-x) y := by rw [inner_sub_left,hxy,sub_zero]
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hsum : inner ℝ (x+y) (A (x+y))=
      inner ℝ x (A x)+2*inner ℝ x (A y)+inner ℝ y (A y) := by
    rw [map_add,inner_add_left,inner_add_right,inner_add_right]
    rw [←hA x y,real_inner_comm y (A x)]
    ring
  have ht : 2*(d/8)*‖x‖*‖y‖≤(d/8)*(‖x‖^2+‖y‖^2) := by
    have hh:2*‖x‖*‖y‖≤‖x‖^2+‖y‖^2:=by nlinarith [sq_nonneg (‖x‖-‖y‖)]
    have hb:=mul_le_mul_of_nonneg_left hh (by positivity : 0≤d/8)
    nlinarith [hb]
  have ha':d*‖y‖^2≤a*‖y‖^2:=mul_le_mul_of_nonneg_right hda (sq_nonneg _)
  have hc':d*‖x‖^2≤c*‖x‖^2:=mul_le_mul_of_nonneg_right hdc (sq_nonneg _)
  have hnn : (d/8)*‖x+y‖^2=(d/8)*(‖x‖^2+‖y‖^2):=congrArg (fun z=>(d/8)*z) hn
  have hn2 : (d/2)*‖x+y‖^2=(d/2)*(‖x‖^2+‖y‖^2):=congrArg (fun z=>(d/2)*z) hn
  have hdxx:0≤d*‖x‖^2:=mul_nonneg hd.le (sq_nonneg _)
  have hdyy:0≤d*‖y‖^2:=mul_nonneg hd.le (sq_nonneg _)
  rw [ContinuousLinearMap.add_apply,inner_add_right]
  nlinarith [(abs_le.mp hcross).1,(abs_le.mp hK).1,hlower y,hbase x]

theorem compressed_pairing (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (K : E→L[ℝ]E) (u : E) :
    inner ℝ u ((W.starProjection.comp (K.comp W.starProjection)) u)=
      inner ℝ (W.starProjection u) (K (W.starProjection u)) := by
  exact (W.inner_starProjection_left_eq_right u (K (W.starProjection u))).symm

/-- This is the quantitative form estimate used after a compact-range
projection has been constructed and its finite action has converged. -/
theorem finite_projection_stability (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (A K : E→L[ℝ]E) {a c d : ℝ} (hd : 0<d) (hda : d≤a) (hdc : d≤c)
    (hA : ∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hlower : ∀x,a*‖x‖^2 ≤ inner ℝ x (A x))
    (hbase : ∀x,c*‖x‖^2≤‖x‖^2+inner ℝ x (K x))
    (hfinite : ∀x∈W,‖A x-x‖≤(d/8)*‖x‖)
    (hcompact : ‖K-W.starProjection.comp (K.comp W.starProjection)‖≤d/8) (u : E) :
    (d/2)*‖u‖^2 ≤ inner ℝ u ((A+K) u) := by
  let x:=W.starProjection u
  let y:=u-x
  have hsum:x+y=u:=add_sub_cancel _ _
  have hxy:inner ℝ x y=0:=by
    rw [real_inner_comm]
    exact W.starProjection_inner_eq_zero u x (W.starProjection_apply_mem u)
  have hK : |inner ℝ (x+y) (K (x+y))-inner ℝ x (K x)|≤(d/8)*‖x+y‖^2 := by
    rw [hsum]
    have he : inner ℝ u (K u)-inner ℝ x (K x)=
        inner ℝ u ((K-W.starProjection.comp (K.comp W.starProjection)) u) := by
      rw [ContinuousLinearMap.sub_apply,inner_sub_right,compressed_pairing]
    rw [he]
    calc
      _≤‖u‖*‖(K-W.starProjection.comp (K.comp W.starProjection)) u‖:=abs_real_inner_le_norm _ _
      _≤‖u‖*(‖K-W.starProjection.comp (K.comp W.starProjection)‖*‖u‖):=
        mul_le_mul_of_nonneg_left ((K-W.starProjection.comp (K.comp W.starProjection)).le_opNorm u) (norm_nonneg _)
      _≤‖u‖*((d/8)*‖u‖):=mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcompact (norm_nonneg _)) (norm_nonneg _)
      _=_:=by ring
  simpa only [hsum] using vector_form_stability A K hd hda hdc hA hlower hbase x y hxy
    (hfinite x (W.starProjection_apply_mem u)) hK

end
end Resonance.ProjectionFormStability
