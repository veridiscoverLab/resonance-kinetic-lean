import Resonance.PinnedSmoothDomain
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The actual maximal integral form: dense domain, closed graph-norm
completeness, and its original full-difference integral. This module does
not identify a smooth form core or assume a representation theorem. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal ComplexConjugate
namespace Resonance.PinnedClosedForm
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedMaximalDifference Resonance.PinnedSmoothDomain

abbrev FormDomain {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (a : FourCircle→ℝ) :=
  (maximalDifference hd0 hdU a).domain

def form {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (a : FourCircle→ℝ) (γ : ℝ)
    (u v : FormDomain hd0 hdU a) : ℂ :=
  (γ/4:ℂ)*inner ℂ ((maximalDifference hd0 hdU a) u)
    ((maximalDifference hd0 hdU a) v)

theorem full_product_integrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (u v : FormDomain hd0 hdU a) :
    Integrable (fun k => conj (difference (u : Source) k)*difference (v : Source) k)
      (weightedCoarea d a) := by
  have hI := L2.integrable_inner (𝕜:=ℂ)
    ((maximalDifference hd0 hdU a) u) ((maximalDifference hd0 hdU a) v)
  apply hI.congr
  filter_upwards [maximalDifference_apply_ae hd0 hdU a u,
    maximalDifference_apply_ae hd0 hdU a v] with k hu hv
  simp only [hu,hv,RCLike.inner_apply]
  ring

/-- Lean uses an inner product conjugate-linear in its first variable;
the displayed integral fixes that convention explicitly. -/
theorem form_integral {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) (u v : FormDomain hd0 hdU a) :
    form hd0 hdU a γ u v = (γ/4:ℂ)*
      ∫ k,conj (difference (u : Source) k)*difference (v : Source) k ∂weightedCoarea d a := by
  unfold form
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [maximalDifference_apply_ae hd0 hdU a u,
    maximalDifference_apply_ae hd0 hdU a v] with k hu hv
  simp only [hu,hv,RCLike.inner_apply]
  ring

theorem full_square_integrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (u : FormDomain hd0 hdU a) :
    Integrable (fun k => ‖difference (u : Source) k‖^2) (weightedCoarea d a) :=
  (memLp_two_iff_integrable_sq_norm
    ((maximalDifference_domain_iff hd0 hdU a u).mp u.property).aestronglyMeasurable).mp
      ((maximalDifference_domain_iff hd0 hdU a u).mp u.property)

theorem operator_norm_square_integral {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (u : FormDomain hd0 hdU a) :
    ‖(maximalDifference hd0 hdU a) u‖^2 =
      ∫ k,‖difference (u : Source) k‖^2 ∂weightedCoarea d a := by
  have hi := L2.inner_def (𝕜:=ℂ)
    ((maximalDifference hd0 hdU a) u) ((maximalDifference hd0 hdU a) u)
  simp only [inner_self_eq_norm_sq_to_K] at hi
  norm_cast at hi
  rw [hi]
  apply integral_congr_ae
  filter_upwards [maximalDifference_apply_ae hd0 hdU a u] with k hk
  rw [hk]

theorem form_diagonal {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) (u : FormDomain hd0 hdU a) :
    (form hd0 hdU a γ u u).re = (γ/4)*
      ∫ k,‖difference (u : Source) k‖^2 ∂weightedCoarea d a := by
  rw [form,inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [operator_norm_square_integral]
  simp

theorem form_nonneg {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) {γ : ℝ} (hγ : 0≤γ) (u : FormDomain hd0 hdU a) :
    0≤(form hd0 hdU a γ u u).re := by
  rw [form_diagonal]
  apply mul_nonneg (div_nonneg hγ (by norm_num))
  exact integral_nonneg (fun _=>sq_nonneg _)

/-- This is the completeness criterion for the maximal form domain in
the graph norm; both limits belong to the same original graph. -/
theorem form_graph_complete {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (u : ℕ→FormDomain hd0 hdU a)
    (hsource : CauchySeq (fun n => (u n : Source)))
    (htarget : CauchySeq (fun n => (maximalDifference hd0 hdU a) (u n))) :
    ∃ v : FormDomain hd0 hdU a,
      Tendsto (fun n => (u n : Source)) atTop (𝓝 (v : Source)) ∧
      Tendsto (fun n => (maximalDifference hd0 hdU a) (u n)) atTop
        (𝓝 ((maximalDifference hd0 hdU a) v)) := by
  obtain ⟨f,hf⟩ := cauchySeq_tendsto_of_complete hsource
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete htarget
  have hm : (f,g)∈maximalGraph d a :=
    (maximalGraph_isClosed hd0 hdU a).mem_of_tendsto (hf.prodMk_nhds hg)
      (Eventually.of_forall (fun n => maximalDifference_apply_ae hd0 hdU a (u n)))
  have hfD : f∈(maximalDifference hd0 hdU a).domain := by
    apply (maximalDifference_domain_iff hd0 hdU a f).mpr
    exact (Lp.memLp g).ae_eq hm
  refine ⟨⟨f,hfD⟩,hf,?_⟩
  change (g : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference f at hm
  have he : g=(maximalDifference hd0 hdU a) ⟨f,hfD⟩ :=
    Lp.ext (hm.trans (maximalDifference_apply_ae hd0 hdU a ⟨f,hfD⟩).symm)
  rwa [← he]

/-- The graph is realized in the genuine Hilbert product, rather than
the maximum norm on an ordinary product. -/
def graphHilbert {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (a : FourCircle→ℝ) :
    Submodule ℂ (WithLp 2 (Source × Target d a)) :=
  (graphSubmodule hd0 hdU a).comap (WithLp.linearEquiv 2 ℂ (Source × Target d a)).toLinearMap

theorem graphHilbert_isClosed {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) : IsClosed
      (graphHilbert hd0 hdU a : Set (WithLp 2 (Source × Target d a))) :=
  (maximalGraph_isClosed hd0 hdU a).preimage (WithLp.prod_continuous_ofLp 2 _ _)

instance graphHilbert_complete {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) : CompleteSpace (graphHilbert hd0 hdU a) :=
  completeSpace_coe_iff_isComplete.mpr (graphHilbert_isClosed hd0 hdU a).isComplete

theorem graphHilbert_norm_square {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (u : graphHilbert hd0 hdU a) :
    ‖u‖^2=‖(WithLp.ofLp (u : WithLp 2 (Source × Target d a))).1‖^2+
      ∫ k,‖difference ((WithLp.ofLp (u : WithLp 2 (Source × Target d a))).1) k‖^2
        ∂weightedCoarea d a := by
  let f : Source := (WithLp.ofLp (u : WithLp 2 (Source × Target d a))).1
  let g : Target d a := (WithLp.ofLp (u : WithLp 2 (Source × Target d a))).2
  have hu : (g : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference f := u.property
  have hfD : f∈(maximalDifference hd0 hdU a).domain :=
    (maximalDifference_domain_iff hd0 hdU a f).mpr ((Lp.memLp g).ae_eq hu)
  have he : g=(maximalDifference hd0 hdU a) ⟨f,hfD⟩ :=
    Lp.ext (hu.trans (maximalDifference_apply_ae hd0 hdU a ⟨f,hfD⟩).symm)
  change ‖(u : WithLp 2 (Source × Target d a))‖^2=‖f‖^2+_
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖f‖^2+‖g‖^2=‖f‖^2+_
  rw [he,operator_norm_square_integral]

end
end Resonance.PinnedClosedForm
