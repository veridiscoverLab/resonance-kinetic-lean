import Resonance.SpacetimeMultiplierOperators
import Resonance.HilbertOperatorConvergence

/-! Complete-current convergence on the original common spacetime quartet
measure. The source weak limit and entropy norm limit are explicit premises
here; the actual equation and entropy balance must establish them. Global
uniform smallness of the coefficients is not required. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology
namespace Resonance.SpacetimeCurrentConvergence
noncomputable section
open SpacetimePairing SpacetimeReference SpacetimeRootMultiplier
open SpacetimeMultiplierOperators LpOperators LpFixedTestOperators
variable {R : ℝ} (hR : 0<R) (T : ℝ) {K : Set Thermodynamics.Parameter}
  (hK : IsCompact K) (hpos : K⊆Thermodynamics.positiveDomain R)
  {θ : Base→Thermodynamics.Parameter} (hm : Measurable θ)
  (hθ : ∀ᵐz∂baseMeasure T,θ z∈K)
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
  {b d : ι→Source→ℝ} {C : ℝ} (hC : 1≤C)
  (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
  (hd : ∀n,AEStronglyMeasurable (d n) (sourceMeasure R T))
  (hbnd : ∀n,∀ᵐz∂sourceMeasure R T,|b n z|≤C)
  (hdnd : ∀n,∀ᵐz∂sourceMeasure R T,|d n z|≤C)

def current (n : ι) (x : Space R T) : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ) :=
  multiplyCLM (root_memLp hR.le T θ (hb n) (hbnd n))
    (SpacetimeDifference.physicalDifference hR T hK hpos hm hθ
      (multiplyCLM (source_memLp hR T (hd n) (hdnd n)) x))

theorem current_ae (n : ι) (x : Space R T) :
    current hR T hK hpos hm hθ hb hd hbnd hdnd n x=ᵐ[SpacetimeRJMeasure.measure R T θ]
      (fun p=>root (b n) p*SpacetimeDifference.physicalRaw (θ:=θ) (fun z=>x z*d n z) p) := by
  let Bx:=multiplyCLM (source_memLp hR T (hd n) (hdnd n)) x
  have hx : (Bx:Source→ℝ)=ᵐ[reference R T](fun z=>x z*d n z):=
    multiply_ae (source_memLp hR T (hd n) (hdnd n)) x
  have hh:=SpacetimeDifference.physicalDifference_ae hR T hK hpos hm hθ Bx
  have hout:=multiply_ae (root_memLp hR.le T θ (hb n) (hbnd n))
    (SpacetimeDifference.physicalDifference hR T hK hpos hm hθ Bx)
  filter_upwards [hout,hh,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 0).ae_eq hx,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 1).ae_eq hx,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 2).ae_eq hx,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 3).ae_eq hx]
    with p ho hr h0 h1 h2 h3
  change multiply (root_memLp hR.le T θ (hb n) (hbnd n))
    (SpacetimeDifference.physicalDifference hR T hK hpos hm hθ Bx) p=_
  rw [ho,hr,mul_comm]
  simp only [Function.comp_def] at h0 h1 h2 h3
  simp only [SpacetimeDifference.physicalRaw,SpacetimeDifference.rawDifference,h0,h1,h2,h3]

include hR hK hpos hm hθ hb hd hbnd hdnd in
theorem current_square_integrable (n : ι) (x : Space R T) :
    Integrable (fun p=>(root (b n) p)^2*
      (SpacetimeDifference.physicalRaw (θ:=θ) (fun z=>x z*d n z) p)^2)
      (SpacetimeRJMeasure.measure R T θ) := by
  have hi:=(Lp.memLp (current hR T hK hpos hm hθ hb hd hbnd hdnd n x)).integrable_norm_pow
    (by norm_num)
  apply hi.congr
  filter_upwards [current_ae hR T hK hpos hm hθ hb hd hbnd hdnd n x] with p hp
  rw [hp,Real.norm_eq_abs,sq_abs,mul_pow]

theorem current_square_integral (n : ι) (x : Space R T) :
    ‖current hR T hK hpos hm hθ hb hd hbnd hdnd n x‖^2=
      ∫p,(root (b n) p)^2*
        (SpacetimeDifference.physicalRaw (θ:=θ) (fun z=>x z*d n z) p)^2
        ∂SpacetimeRJMeasure.measure R T θ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [current_ae hR T hK hpos hm hθ hb hd hbnd hdnd n x] with p hp
  change current hR T hK hpos hm hθ hb hd hbnd hdnd n x p*
    current hR T hK hpos hm hθ hb hd hbnd hdnd n x p=_
  rw [hp]
  ring

include hC in
theorem weak_current
    (hbconv : TendstoInMeasure (sourceMeasure R T) b l (fun _=>1))
    (hdconv : TendstoInMeasure (sourceMeasure R T) d l (fun _=>1))
    {x : ι→Space R T} {u : Space R T} {Cx : ℝ}
    (hxb : ∀n,‖x n‖≤Cx)
    (hxw : ∀v:Space R T,Tendsto (fun n=>inner ℝ (x n) v) l (𝓝 (inner ℝ u v))) :
    ∀V:Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ),
      Tendsto (fun n=>inner ℝ (current hR T hK hpos hm hθ hb hd hbnd hdnd n (x n)) V) l
        (𝓝 (inner ℝ (SpacetimeDifference.physicalDifference hR T hK hpos hm hθ u) V)) := by
  let RR:=SpacetimeDifference.physicalDifference hR T hK hpos hm hθ
  let A n:=multiplyCLM (root_memLp hR.le T θ (hb n) (hbnd n))
  let B n:=multiplyCLM (source_memLp hR T (hd n) (hdnd n))
  have hone : ∀ᵐz∂sourceMeasure R T,|(1:ℝ)|≤C:=ae_of_all _ (fun _=>by simpa using hC)
  have hAf : ∀V,Tendsto (fun n=>A n V) l (𝓝 V) := by
    intro V
    have hh:=root_fixed_test_operator_strong hR.le T θ hb aestronglyMeasurable_const
      hbnd hone hbconv V
    have he:=multiply_eq_id (root_memLp hR.le T θ aestronglyMeasurable_const hone)
      (ae_of_all _ (fun _=>by simp [root]))
    simpa only [he,ContinuousLinearMap.one_apply] using hh
  have hBf : ∀v,Tendsto (fun n=>B n v) l (𝓝 v) := by
    intro v
    have hh:=source_fixed_test_strong hR T hd aestronglyMeasurable_const hdnd hone hdconv v
    have he:=multiply_eq_id (source_memLp hR T aestronglyMeasurable_const hone)
      (ae_of_all _ (fun _=>rfl))
    simpa only [he,ContinuousLinearMap.one_apply] using hh
  have hBn : ∀n,‖B n‖≤C := by
    intro n
    exact multiply_norm_bound _ (by linarith)
      ((reference_volume_equivalent hR T).1.ae_le (hdnd n))
  have hh:=HilbertOperatorConvergence.weak_sandwich hxb hxw RR B 1 A 1 hBn
    (fun _=>multiply_symmetric _) (by intros; rfl)
    (fun _=>multiply_symmetric _) (by intros; rfl) hBf hAf
  simpa only [ContinuousLinearMap.one_apply] using hh

include hC in
theorem strong_current
    (hbconv : TendstoInMeasure (sourceMeasure R T) b l (fun _=>1))
    (hdconv : TendstoInMeasure (sourceMeasure R T) d l (fun _=>1))
    {x : ι→Space R T} {u : Space R T} {Cx : ℝ}
    (hxb : ∀n,‖x n‖≤Cx)
    (hxw : ∀v:Space R T,Tendsto (fun n=>inner ℝ (x n) v) l (𝓝 (inner ℝ u v)))
    (hnorm : Tendsto
      (fun n=>‖current hR T hK hpos hm hθ hb hd hbnd hdnd n (x n)‖^2) l
      (𝓝 (‖SpacetimeDifference.physicalDifference hR T hK hpos hm hθ u‖^2))) :
    Tendsto (fun n=>current hR T hK hpos hm hθ hb hd hbnd hdnd n (x n)) l
      (𝓝 (SpacetimeDifference.physicalDifference hR T hK hpos hm hθ u)) :=
  HilbertCurrentConvergence.strong_of_weak_and_norm_square
    (weak_current hR T hK hpos hm hθ hC hb hd hbnd hdnd hbconv hdconv hxb hxw) hnorm

end
end Resonance.SpacetimeCurrentConvergence
