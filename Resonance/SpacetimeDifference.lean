import Resonance.SpacetimeProfileBounds

/-! The complete dynamic reciprocal difference, as a genuine bounded
linear map on the common reference-frequency space. Its adjoint is a
bounded functional return in that fixed Hilbert metric; it is not silently
identified with an unweighted pointwise collision output. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace Resonance.SpacetimeDifference
noncomputable section
open ResonantMeasure Thermodynamics WeightedJointMeasure SpacetimePairing
open SpacetimeReference SpacetimeProfileBounds LpOperators

def rawDifference (f : Source→ℝ) (p : Joint) : ℝ :=
  (1/2:ℝ)*(f (leg 0 p)+f (leg 1 p)-f (leg 2 p)-f (leg 3 p))

def fullDifference {R : ℝ} (hR : 0≤R) (T : ℝ) : Space R T→L[ℝ]Raw R T :=
  (1/2:ℝ) • (pullback hR T 0+pullback hR T 1-pullback hR T 2-pullback hR T 3)

theorem fullDifference_ae {R : ℝ} (hR : 0≤R) (T : ℝ) (u : Space R T) :
    fullDifference hR T u=ᵐ[SpacetimePairing.jointMeasure R T]rawDifference u := by
  let a:=pullback hR T 0 u
  let b:=pullback hR T 1 u
  let c:=pullback hR T 2 u
  let d:=pullback hR T 3 u
  change ((1/2:ℝ) • (a+b-c-d):Raw R T)=ᵐ[_]rawDifference u
  filter_upwards [pullback_ae hR T 0 u,pullback_ae hR T 1 u,pullback_ae hR T 2 u,
    pullback_ae hR T 3 u,Lp.coeFn_add a b,Lp.coeFn_sub (a+b) c,
    Lp.coeFn_sub (a+b-c) d,Lp.coeFn_smul (1/2:ℝ) (a+b-c-d)]
    with p h0 h1 h2 h3 ha hb hc hd
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply] at ha hb hc hd
  rw [hd,hc,hb,ha]
  change (1/2:ℝ)*((pullback hR T 0 u) p+(pullback hR T 1 u) p-
    (pullback hR T 2 u) p-(pullback hR T 3 u) p)=rawDifference u p
  rw [h0,h1,h2,h3]
  rfl

variable {R : ℝ} (hR : 0<R) (T : ℝ) {K : Set Parameter}
variable (hK : IsCompact K) (hpos : K⊆positiveDomain R) {θ : Base→Parameter}
variable (hm : Measurable θ) (hθ : ∀ᵐz∂baseMeasure T,θ z∈K)

def physicalDifference : Space R T→L[ℝ]Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ) :=
  (changeCLM (measure_domination hR.le T hK hpos hθ).choose_spec.1
    (measure_domination hR.le T hK hpos hθ).choose_spec.2).comp
      ((fullDifference hR.le T).comp
        (multiplyCLM (inverseProfile_memLp hR.le T hK hpos hm hθ)))

def physicalRaw (u : Source→ℝ) (p : Joint) : ℝ :=
  rawDifference (fun z=>u z/profile (θ z.1) z.2) p

theorem physicalDifference_ae (u : Space R T) :
    physicalDifference hR T hK hpos hm hθ u=ᵐ[SpacetimeRJMeasure.measure R T θ]physicalRaw (θ:=θ) u := by
  let g:=multiply (inverseProfile_memLp hR.le T hK hpos hm hθ) u
  have hac:=SpacetimeRJMeasure.measure_absolutelyContinuous R T θ
  have hg : (g:Source→ℝ)=ᵐ[reference R T](fun z=>u z/profile (θ z.1) z.2) := by
    exact (multiply_ae (inverseProfile_memLp hR.le T hK hpos hm hθ) u).mono
      (fun z hz=>hz.trans (div_eq_mul_inv (u z) (profile (θ z.1) z.2)).symm)
  have ho:=changeMeasure_ae (measure_domination hR.le T hK hpos hθ).choose_spec.1
    (measure_domination hR.le T hK hpos hθ).choose_spec.2 (fullDifference hR.le T g)
  filter_upwards [ho,hac.ae_eq (fullDifference_ae hR.le T g),
    (weighted_leg_reference hR T θ 0).ae_eq hg,(weighted_leg_reference hR T θ 1).ae_eq hg,
    (weighted_leg_reference hR T θ 2).ae_eq hg,(weighted_leg_reference hR T θ 3).ae_eq hg]
    with p hout hfull h0 h1 h2 h3
  change changeMeasure (measure_domination hR.le T hK hpos hθ).choose_spec.1
    (measure_domination hR.le T hK hpos hθ).choose_spec.2
      (fullDifference hR.le T g) p=physicalRaw (θ:=θ) u p
  rw [hout,hfull]
  simp only [Function.comp_def] at h0 h1 h2 h3
  simp only [rawDifference,physicalRaw,h0,h1,h2,h3]

include hR hK hpos hm hθ in
theorem physical_square_integrable (u : Space R T) :
    Integrable (fun p=>(physicalRaw (θ:=θ) u p)^2) (SpacetimeRJMeasure.measure R T θ) := by
  have hh:=(Lp.memLp (physicalDifference hR T hK hpos hm hθ u)).integrable_norm_pow
    (by norm_num)
  apply hh.congr
  filter_upwards [physicalDifference_ae hR T hK hpos hm hθ u] with p hp
  rw [hp,Real.norm_eq_abs,sq_abs]

theorem physical_square_integral (u : Space R T) :
    ‖physicalDifference hR T hK hpos hm hθ u‖^2=
      ∫p,(physicalRaw (θ:=θ) u p)^2∂SpacetimeRJMeasure.measure R T θ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [physicalDifference_ae hR T hK hpos hm hθ u] with p hp
  change physicalDifference hR T hK hpos hm hθ u p*
    physicalDifference hR T hK hpos hm hθ u p=_
  rw [hp,pow_two]

theorem transpose_pairing (J : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)) (u : Space R T) :
    inner ℝ u ((physicalDifference hR T hK hpos hm hθ).adjoint J)=
      ∫p,J p*physicalRaw (θ:=θ) u p∂SpacetimeRJMeasure.measure R T θ := by
  rw [ContinuousLinearMap.adjoint_inner_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [physicalDifference_ae hR T hK hpos hm hθ u] with p hp
  change J p*physicalDifference hR T hK hpos hm hθ u p=_
  rw [hp]

theorem transpose_strong_return {ι : Type*} {l : Filter ι}
    {J : ι→Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)}
    {J₀ : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ)} (hJ : Tendsto J l (nhds J₀)) :
    Tendsto (fun n=>(physicalDifference hR T hK hpos hm hθ).adjoint (J n)) l
      (nhds ((physicalDifference hR T hK hpos hm hθ).adjoint J₀)) :=
  (physicalDifference hR T hK hpos hm hθ).adjoint.continuous.tendsto J₀ |>.comp hJ

end
end Resonance.SpacetimeDifference
