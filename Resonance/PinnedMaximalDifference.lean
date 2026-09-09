import Resonance.PinnedLegACCircle

/-! The maximal full four-leg difference, in the actual weighted coarea L²
space.  Closedness does not assert a C² core, dense domain, or spectral gap. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Resonance.PinnedMaximalDifference
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedEndToEnd
open Resonance.PinnedMeasureNormalization Resonance.PinnedClassificationFinal
open Resonance.PinnedLegACCircle

abbrev FourCircle := Fin 4 → PinnedPeriodicity.Circle
def fullLegs (k : CircleMomenta) : FourCircle := fun i => circleLeg i k
def weight (a : FourCircle→ℝ) (k : CircleMomenta) : ℝ≥0∞ := ENNReal.ofReal (a (fullLegs k))
def weightedCoarea (d : ℝ) (a : FourCircle→ℝ) : Measure CircleMomenta :=
  (euclideanCircleRegularCoarea d).withDensity (weight a)
abbrev Source := Lp ℂ 2 circleHaar
abbrev Target (d : ℝ) (a : FourCircle→ℝ) := Lp ℂ 2 (weightedCoarea d a)

def difference (φ : PinnedPeriodicity.Circle→ℂ) (k : CircleMomenta) : ℂ :=
  φ (circleLeg 0 k)+φ (circleLeg 1 k)-φ (circleLeg 2 k)-φ (circleLeg 3 k)

theorem weighted_ae_comp {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (i : Fin 4) {p : PinnedPeriodicity.Circle→Prop}
    (hp : ∀ᵐ x ∂circleHaar, p x) :
    ∀ᵐ k ∂weightedCoarea d a, p (circleLeg i k) :=
  (withDensity_absolutelyContinuous _ _).ae_le (full_coarea_ae_comp hd0 hdU i hp)

def maximalGraph (d : ℝ) (a : FourCircle→ℝ) : Set (Source × Target d a) :=
  {p | (p.2 : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference p.1}

theorem maximalGraph_isClosed {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) : IsClosed (maximalGraph d a) := by
  apply IsSeqClosed.isClosed
  intro u p hu ht
  have hx : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp ht
  obtain ⟨r,hr,hxr⟩ := (tendstoInMeasure_of_tendsto_Lp hx).exists_seq_tendsto_ae
  have hy : Tendsto (fun n => (u (r n)).2) atTop (𝓝 p.2) :=
    (continuous_snd.continuousAt.tendsto.comp ht).comp hr.tendsto_atTop
  obtain ⟨s,hs,hys⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
  have hrel : ∀ᵐ k ∂weightedCoarea d a, ∀ n : ℕ,
      (u (r (s n))).2 k = difference (u (r (s n))).1 k :=
    ae_all_iff.mpr (fun n => hu (r (s n)))
  filter_upwards [hys,hrel,weighted_ae_comp hd0 hdU a 0 hxr,
    weighted_ae_comp hd0 hdU a 1 hxr,weighted_ae_comp hd0 hdU a 2 hxr,
    weighted_ae_comp hd0 hdU a 3 hxr] with k hyk hrelk h0 h1 h2 h3
  have hdelta : Tendsto (fun n => difference (u (r (s n))).1 k) atTop
      (𝓝 (difference p.1 k)) :=
    ((((h0.comp hs.tendsto_atTop).add (h1.comp hs.tendsto_atTop)).sub
      (h2.comp hs.tendsto_atTop)).sub (h3.comp hs.tendsto_atTop))
  have hyk' : Tendsto (fun n => (u (r (s n))).2 k) atTop
      (𝓝 (difference p.1 k)) :=
    hdelta.congr' (Eventually.of_forall (fun n => (hrelk n).symm))
  exact tendsto_nhds_unique hyk hyk'

theorem maximalGraph_vertical_unique (d : ℝ) (a : FourCircle→ℝ)
    {f : Source} {g h : Target d a}
    (hg : (f,g)∈maximalGraph d a) (hh : (f,h)∈maximalGraph d a) : g=h := by
  change (g : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference f at hg
  change (h : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference f at hh
  exact Lp.ext (hg.trans hh.symm)

theorem difference_ae_congr {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) {φ ψ : PinnedPeriodicity.Circle→ℂ}
    (he : φ =ᵐ[circleHaar] ψ) :
    difference φ =ᵐ[weightedCoarea d a] difference ψ := by
  filter_upwards [weighted_ae_comp hd0 hdU a 0 he,weighted_ae_comp hd0 hdU a 1 he,
    weighted_ae_comp hd0 hdU a 2 he,weighted_ae_comp hd0 hdU a 3 he] with k h0 h1 h2 h3
  simp only [difference,h0,h1,h2,h3]

def graphSubmodule {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (a : FourCircle→ℝ) :
    Submodule ℂ (Source × Target d a) where
  carrier := maximalGraph d a
  zero_mem' := by
    have hz := difference_ae_congr hd0 hdU a (Lp.coeFn_zero ℂ 2 circleHaar)
    filter_upwards [hz,Lp.coeFn_zero ℂ 2 (weightedCoarea d a)] with k h1 h2
    change (0 : Target d a) k=difference (0 : Source) k
    rw [h1,h2]
    simp [difference]
  add_mem' := by
    intro p q hp hq
    change (p.2 : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference p.1 at hp
    change (q.2 : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference q.1 at hq
    have hd := difference_ae_congr hd0 hdU a (Lp.coeFn_add p.1 q.1)
    filter_upwards [hp,hq,hd,Lp.coeFn_add p.2 q.2] with k hp hq hd ht
    change (p.2+q.2) k=difference ((p.1+q.1 : Source) : PinnedPeriodicity.Circle→ℂ) k
    rw [hd,ht]
    simp only [Pi.add_apply,hp,hq,difference]
    ring
  smul_mem' := by
    intro c p hp
    change (p.2 : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference p.1 at hp
    have hd := difference_ae_congr hd0 hdU a (Lp.coeFn_smul c p.1)
    filter_upwards [hp,hd,Lp.coeFn_smul c p.2] with k hp hd ht
    change (c • p.2) k=difference ((c • p.1 : Source) : PinnedPeriodicity.Circle→ℂ) k
    rw [hd,ht]
    simp only [Pi.smul_apply,smul_eq_mul,hp,difference]
    ring

theorem graphSubmodule_zero_fiber {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (p : Source × Target d a)
    (hp : p∈graphSubmodule hd0 hdU a) (h0 : p.1=0) : p.2=0 := by
  apply maximalGraph_vertical_unique d a
  · exact hp
  · rw [h0]
    exact (graphSubmodule hd0 hdU a).zero_mem

/-- The actual maximal partially defined linear map.  The graph criterion
required by `toLinearPMap` is proved, so its zero-map fallback is excluded. -/
def maximalDifference {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (a : FourCircle→ℝ) :
    Source →ₗ.[ℂ] Target d a := (graphSubmodule hd0 hdU a).toLinearPMap

theorem maximalDifference_graph {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) :
    (maximalDifference hd0 hdU a).graph=graphSubmodule hd0 hdU a :=
  (graphSubmodule hd0 hdU a).toLinearPMap_graph_eq (graphSubmodule_zero_fiber hd0 hdU a)

theorem maximalDifference_isClosed {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) : (maximalDifference hd0 hdU a).IsClosed := by
  rw [LinearPMap.IsClosed,maximalDifference_graph]
  exact maximalGraph_isClosed hd0 hdU a

/-- Only the complete difference is required in L².  There is no assumption
that any individual pulled-back leg is square integrable. -/
theorem maximalDifference_domain_iff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (f : Source) :
    f∈(maximalDifference hd0 hdU a).domain ↔
      MemLp (difference f) 2 (weightedCoarea d a) := by
  change f∈(graphSubmodule hd0 hdU a).map (LinearMap.fst ℂ Source (Target d a)) ↔ _
  constructor
  · rintro ⟨⟨g,h⟩,hp,he⟩
    change g=f at he
    subst g
    change (h : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a] difference f at hp
    exact (Lp.memLp h).ae_eq hp
  · intro hf
    exact ⟨(f,hf.toLp (difference f)),hf.coeFn_toLp,rfl⟩

theorem maximalDifference_apply_ae {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (f : (maximalDifference hd0 hdU a).domain) :
    ((maximalDifference hd0 hdU a) f : CircleMomenta→ℂ) =ᵐ[weightedCoarea d a]
      difference (f : Source) := by
  have h := (maximalDifference hd0 hdU a).mem_graph f
  rw [maximalDifference_graph] at h
  exact h

theorem fullLegs_continuous : Continuous fullLegs :=
  continuous_pi (fun i => circleLeg_continuous i)

theorem coarea_absolutelyContinuous_weighted (d : ℝ) (a : FourCircle→ℝ)
    (ha : Continuous a) (haPos : ∀ x, 0<a x) :
    euclideanCircleRegularCoarea d ≪ weightedCoarea d a := by
  apply withDensity_absolutelyContinuous'
  · exact (ENNReal.continuous_ofReal.comp (ha.comp fullLegs_continuous)).measurable.aemeasurable
  · exact Eventually.of_forall (fun k => (ENNReal.ofReal_pos.mpr (haPos (fullLegs k))).ne')

theorem difference_zero_iff (φ : PinnedPeriodicity.Circle→ℂ) (k : CircleMomenta) :
    difference φ k=0 ↔ circleInvariantRelation φ k := by
  change φ (circleLeg 0 k)+φ (circleLeg 1 k)-φ (circleLeg 2 k)-φ (circleLeg 3 k)=0 ↔
    φ (circleLeg 0 k)+φ (circleLeg 1 k)=φ (circleLeg 2 k)+φ (circleLeg 3 k)
  rw [sub_sub,sub_eq_zero]

theorem maximalGraph_kernel_classification {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (ha : Continuous a) (haPos : ∀ x, 0<a x) (f : Source) :
    (f,0)∈maximalGraph d a ↔
      ∃! AB : ℂ × ℂ, (f : PinnedPeriodicity.Circle→ℂ) =ᵐ[circleHaar]
        (fun k => AB.1+AB.2*(circleDispersion d k : ℂ)) := by
  constructor
  · intro hf
    have hdiff : ∀ᵐ k ∂weightedCoarea d a, difference f k=0 := by
      change (0 : Target d a) =ᵐ[weightedCoarea d a] difference f at hf
      filter_upwards [hf,Lp.coeFn_zero ℂ 2 (weightedCoarea d a)] with k h1 h2
      exact h1.symm.trans h2
    have hi : euclideanCircleInvariant d f := by
      filter_upwards [(coarea_absolutelyContinuous_weighted d a ha haPos).ae_le hdiff] with k hk
      exact (difference_zero_iff f k).mp hk
    exact euclidean_coarea_classification_unique hd0 hdU f
      (Lp.aestronglyMeasurable f).aemeasurable hi
  · rintro ⟨AB,hAB,_⟩
    have hi : euclideanCircleInvariant d f :=
      (full_coarea_invariant_iff_of_ae_eq hd0 hdU hAB).mpr
        (affine_representative_euclidean_invariant hd0 hdU AB.1 AB.2)
    have hdiff : ∀ᵐ k ∂weightedCoarea d a, difference f k=0 := by
      filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hi] with k hk
      exact (difference_zero_iff f k).mpr hk
    filter_upwards [hdiff,Lp.coeFn_zero ℂ 2 (weightedCoarea d a)] with k h1 h2
    exact h2.trans h1.symm

theorem maximalDifference_kernel_iff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (ha : Continuous a) (haPos : ∀ x, 0<a x) (f : Source) :
    (∃ hf : f∈(maximalDifference hd0 hdU a).domain,
      maximalDifference hd0 hdU a ⟨f,hf⟩=0) ↔
      ∃! AB : ℂ × ℂ, (f : PinnedPeriodicity.Circle→ℂ) =ᵐ[circleHaar]
        (fun k => AB.1+AB.2*(circleDispersion d k : ℂ)) := by
  rw [← maximalGraph_kernel_classification hd0 hdU a ha haPos f]
  constructor
  · rintro ⟨hf,hzero⟩
    have hg := (maximalDifference hd0 hdU a).mem_graph ⟨f,hf⟩
    rw [maximalDifference_graph,hzero] at hg
    exact hg
  · intro hg
    have hg' : (f,0)∈(maximalDifference hd0 hdU a).graph := by
      rw [maximalDifference_graph]
      exact hg
    obtain ⟨⟨g,hgdom⟩,he,hval⟩ := (LinearPMap.mem_graph_iff _).mp hg'
    change g=f at he
    subst g
    exact ⟨hgdom,hval⟩

end
end Resonance.PinnedMaximalDifference
