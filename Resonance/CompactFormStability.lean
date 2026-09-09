import Resonance.CompactOrthogonalApproximation
import Resonance.StrongCompactConvergence

/-! Stability of a positive identity-plus-compact form under a uniformly
positive, uniformly bounded diagonal converging only strongly to identity.
The theorem is on one fixed Hilbert space. Original collision multipliers
must satisfy its explicit operator hypotheses through their actual geometry. -/
open Set Filter
open scoped InnerProductSpace Topology
namespace Resonance.CompactFormStability
noncomputable section
open ProjectionFormStability CompactOrthogonalApproximation StrongCompactConvergence
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 2200000

theorem compression_form_error (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (K : E→L[ℝ]E) (hK : ∀x y,inner ℝ (K x) y=inner ℝ x (K y))
    {ε : ℝ} (hε : 0≤ε) (happrox : ‖K-W.starProjection.comp K‖≤ε) (u : E) :
    |inner ℝ u (K u)-inner ℝ (W.starProjection u) (K (W.starProjection u))|
      ≤2*ε*‖u‖^2 := by
  let x:=W.starProjection u
  let y:=u-x
  let B:=K-W.starProjection.comp K
  have hx:‖x‖≤‖u‖:=W.norm_starProjection_apply_le u
  have hxy:inner ℝ x y=0:=by
    rw [real_inner_comm]
    exact W.starProjection_inner_eq_zero u x (W.starProjection_apply_mem u)
  have hsum:x+y=u:=add_sub_cancel _ _
  have hy:‖y‖≤‖u‖:=by
    have hn:=orthogonal_sum_norm x y hxy
    rw [hsum] at hn
    nlinarith [norm_nonneg y,norm_nonneg u,sq_nonneg ‖x‖]
  have hzero:inner ℝ (W.starProjection (K x)) y=0:=by
    rw [real_inner_comm]
    exact W.starProjection_inner_eq_zero u _ (W.starProjection_apply_mem _)
  have h1:inner ℝ u (B u)=inner ℝ u (K u)-inner ℝ x (K u):=by
    change inner ℝ u (K u-W.starProjection (K u))=_
    rw [inner_sub_right,←W.inner_starProjection_left_eq_right u (K u)]
  have h2:inner ℝ (B x) y=inner ℝ x (K u)-inner ℝ x (K x):=by
    change inner ℝ (K x-W.starProjection (K x)) y=_
    rw [inner_sub_left,hzero,sub_zero,hK x y]
    change inner ℝ x (K (u-x))=_
    rw [map_sub,inner_sub_right]
  have he:inner ℝ u (K u)-inner ℝ x (K x)=inner ℝ u (B u)+inner ℝ (B x) y:=by
    rw [h1,h2]
    ring
  have hb (v:E):‖B v‖≤ε*‖v‖:=((B.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right happrox (norm_nonneg _)))
  have hfirst:|inner ℝ u (B u)|≤ε*‖u‖^2:=by
    exact (abs_real_inner_le_norm _ _).trans (by
      have hh:=mul_le_mul_of_nonneg_left (hb u) (norm_nonneg u)
      simpa only [pow_two,mul_left_comm,mul_assoc] using hh)
  have hsecond:|inner ℝ (B x) y|≤ε*‖u‖^2:=by
    calc
      _≤‖B x‖*‖y‖:=abs_real_inner_le_norm _ _
      _≤(ε*‖x‖)*‖y‖:=mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
      _≤(ε*‖u‖)*‖u‖:=mul_le_mul (mul_le_mul_of_nonneg_left hx hε) hy
        (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))
      _=_:=by ring
  change |inner ℝ u (K u)-inner ℝ x (K x)|≤_
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

theorem spanProjection_compact (s : Finset E) : IsCompactOperator (spanProjection s) := by
  let W:=Submodule.span ℝ (s:Set E)
  exact (isCompactOperator_of_locallyCompactSpace_dom W.orthogonalProjection).clm_comp W.subtypeL

/-- The hard finite projection and compact-image uniformity are produced
inside this proof. Strong convergence is sufficient; no operator-norm
convergence of A to identity is assumed. -/
theorem eventual_form_coercivity (K : E→L[ℝ]E) (hKc : IsCompactOperator K)
    (hKs : ∀x y,inner ℝ (K x) y=inner ℝ x (K y))
    (A : I→E→L[ℝ]E) (l : Filter I) {a c B : ℝ}
    (ha : 0<a) (hc : 0<c) (hB : 0≤B)
    (hAs : ∀i x y,inner ℝ (A i x) y=inner ℝ x (A i y))
    (hlower : ∀i x,a*‖x‖^2 ≤ inner ℝ x (A i x))
    (hbase : ∀x,c*‖x‖^2≤‖x‖^2+inner ℝ x (K x))
    (hbound : ∀ᶠi in l,‖A i‖≤B)
    (hstrong : ∀x,Tendsto (fun i=>A i x) l (𝓝 x)) :
    ∀ᶠi in l,∀u,(min a c/2)*‖u‖^2 ≤ inner ℝ u ((A i+K) u) := by
  let d:=min a c
  have hd:0<d:=lt_min ha hc
  obtain ⟨s,hs⟩:=compact_range_projection K hKc (show 0<d/16 by positivity)
  let W:=Submodule.span ℝ (s:Set E)
  let T (i:I):E→L[ℝ]E:=A i-1
  have hTb : ∀ᶠi in l,‖T i‖≤B+1:=by
    filter_upwards [hbound] with i hi
    exact (norm_sub_le (A i) 1).trans (add_le_add hi ContinuousLinearMap.norm_id_le)
  have hTs : ∀x,Tendsto (fun i=>T i x) l (𝓝 (0:E)):=by
    intro x
    simpa only [T,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_self] using
      (hstrong x).sub (tendsto_const_nhds (x:=x))
  have hconv:=compact_image_operator_norm_tendsto (spanProjection s) (spanProjection_compact s)
    T l (show 0≤B+1 by linarith) hTb hTs
  filter_upwards [hconv.eventually (gt_mem_nhds (show 0<d/8 by positivity))] with i hi
  intro u
  let x:=W.starProjection u
  let y:=u-x
  have hsum:x+y=u:=add_sub_cancel _ _
  have hxy:inner ℝ x y=0:=by
    rw [real_inner_comm]
    exact W.starProjection_inner_eq_zero u x (W.starProjection_apply_mem u)
  have hpx:W.starProjection x=x:=W.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem u)
  have hx:‖A i x-x‖≤(d/8)*‖x‖:=by
    have he : (T i).comp (spanProjection s) x=A i x-x:=by
      change A i (W.starProjection x)-W.starProjection x=_
      rw [hpx]
    rw [←he]
    exact (((T i).comp (spanProjection s)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hi.le (norm_nonneg _))
  have hcomp:|inner ℝ (x+y) (K (x+y))-inner ℝ x (K x)|≤(d/8)*‖x+y‖^2:=by
    rw [hsum]
    have hh:=compression_form_error W K hKs (show 0≤d/16 by positivity) hs u
    simpa only [show 2*(d/16)=d/8 by ring] using hh
  simpa only [hsum] using vector_form_stability (A i) K hd (min_le_left a c) (min_le_right a c)
    (hAs i) (hlower i) hbase x y hxy hx hcomp

/-- An additional signed, not necessarily self-adjoint, small operator
is allowed. This is the slot for the actual full marked cross error. -/
theorem eventual_perturbed_coercivity (K : E→L[ℝ]E) (hKc : IsCompactOperator K)
    (hKs : ∀x y,inner ℝ (K x) y=inner ℝ x (K y))
    (A V : I→E→L[ℝ]E) (l : Filter I) {a c B : ℝ}
    (ha : 0<a) (hc : 0<c) (hB : 0≤B)
    (hAs : ∀i x y,inner ℝ (A i x) y=inner ℝ x (A i y))
    (hlower : ∀i x,a*‖x‖^2 ≤ inner ℝ x (A i x))
    (hbase : ∀x,c*‖x‖^2≤‖x‖^2+inner ℝ x (K x))
    (hbound : ∀ᶠi in l,‖A i‖≤B)
    (hstrong : ∀x,Tendsto (fun i=>A i x) l (𝓝 x))
    (hV : Tendsto (fun i=>‖V i‖) l (𝓝 0)) :
    ∀ᶠi in l,∀u,(min a c/4)*‖u‖^2 ≤ inner ℝ u ((A i+K+V i) u) := by
  have hd:0<min a c:=lt_min ha hc
  filter_upwards [eventual_form_coercivity K hKc hKs A l ha hc hB hAs hlower hbase hbound hstrong,
    hV.eventually (gt_mem_nhds (show 0<min a c/4 by positivity))] with i hi hvi
  intro u
  have hv : |inner ℝ u (V i u)|≤(min a c/4)*‖u‖^2 := by
    calc
      _≤‖u‖*‖V i u‖:=abs_real_inner_le_norm _ _
      _≤‖u‖*(‖V i‖*‖u‖):=mul_le_mul_of_nonneg_left ((V i).le_opNorm u) (norm_nonneg _)
      _≤‖u‖*((min a c/4)*‖u‖):=mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hvi.le (norm_nonneg _)) (norm_nonneg _)
      _=_:=by ring
  rw [ContinuousLinearMap.add_apply,inner_add_right]
  nlinarith [hi u,(abs_le.mp hv).1]

end
end Resonance.CompactFormStability
