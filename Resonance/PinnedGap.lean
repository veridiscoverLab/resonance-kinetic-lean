import Resonance.PinnedWeightedCompactness
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The spectral gap is derived from the actual full-coarea compactness
theorem and the classified maximal kernel.  No gap or compactness property
is an input.  Energies are extended nonnegative integrals on the whole
regular coarea, not sums of separately assumed single-leg L² norms. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate
namespace Resonance.PinnedGap
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedMeasureNormalization Resonance.PinnedLegACCircle
open Resonance.PinnedMaximalDifference

def energy (d:ℝ) (a:FourCircle→ℝ) (f:Source) : ℝ≥0∞ :=
  ∫⁻k,‖difference f k‖ₑ^2 ∂weightedCoarea d a

def nullSpace {d:ℝ} (hd0:0<d) (hdU:d<1/2) (a:FourCircle→ℝ) : Submodule ℂ Source :=
  (graphSubmodule hd0 hdU a).comap
    ((LinearMap.id:Source→ₗ[ℂ]Source).prod (0:Source→ₗ[ℂ]Target d a))

theorem mem_nullSpace_iff {d:ℝ} (hd0:0<d) (hdU:d<1/2) (a:FourCircle→ℝ) (f:Source) :
    f∈nullSpace hd0 hdU a ↔ (f,0)∈maximalGraph d a := Iff.rfl

theorem nullSpace_isClosed {d:ℝ} (hd0:0<d) (hdU:d<1/2) (a:FourCircle→ℝ) :
    IsClosed (nullSpace hd0 hdU a:Set Source) := by
  change IsClosed ((fun f:Source=>(f,(0:Target d a))) ⁻¹' maximalGraph d a)
  exact (maximalGraph_isClosed hd0 hdU a).preimage (continuous_id.prodMk continuous_const)

instance nullSpace_complete {d:ℝ} (hd0:0<d) (hdU:d<1/2) (a:FourCircle→ℝ) :
    CompleteSpace (nullSpace hd0 hdU a) :=
  (nullSpace_isClosed hd0 hdU a).isComplete.completeSpace_coe

theorem nullSpace_classification {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (ha:Continuous a) (hpos:∀k,0<a k) (f:Source) :
    f ∈ nullSpace hd0 hdU a ↔ ∃! AB : ℂ × ℂ,
      (f:PinnedPeriodicity.Circle→ℂ)=ᵐ[circleHaar]
        (fun k=>AB.1+AB.2*(PinnedEndToEnd.circleDispersion d k:ℂ)) :=
  maximalGraph_kernel_classification hd0 hdU a ha hpos f

theorem difference_aestronglyMeasurable {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (f:Source) : AEStronglyMeasurable (difference f) (weightedCoarea d a) := by
  have hleg (i:Fin 4) : AEStronglyMeasurable (fun k=>f (circleLeg i k)) (weightedCoarea d a) := by
    have hac : (weightedCoarea d a).map (circleLeg i) ≪ circleHaar :=
      ((withDensity_absolutelyContinuous _ _).map (circleLeg_continuous i).measurable).trans
        (full_coarea_all_legs_absolutelyContinuous hd0 hdU i)
    exact ((Lp.aestronglyMeasurable f).mono_ac hac).comp_aemeasurable
      (circleLeg_continuous i).measurable.aemeasurable
  exact (((hleg 0).add (hleg 1)).sub (hleg 2)).sub (hleg 3)

theorem nullSpace_of_tendsto_energy_zero {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) {u:ℕ→Source} {f:Source}
    (hconv:Tendsto u atTop (𝓝 f)) (henergy:Tendsto (fun n=>energy d a (u n)) atTop (𝓝 0)) :
    f∈nullSpace hd0 hdU a := by
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hd : ∀ᵐk∂weightedCoarea d a,
      Tendsto (fun n=>‖difference (u (s n)) k‖ₑ^2) atTop (𝓝 (‖difference f k‖ₑ^2)) := by
    filter_upwards [weighted_ae_comp hd0 hdU a 0 hae,weighted_ae_comp hd0 hdU a 1 hae,
      weighted_ae_comp hd0 hdU a 2 hae,weighted_ae_comp hd0 hdU a 3 hae] with k h0 h1 h2 h3
    have he : Tendsto (fun n=>difference (u (s n)) k) atTop (𝓝 (difference f k)) :=
      ((h0.add h1).sub h2).sub h3
    simpa [Function.comp_def,ENNReal.rpow_natCast] using
      (ENNReal.continuous_rpow_const (y:=2)).continuousAt.tendsto.comp he.enorm
  have hlim : energy d a f≤liminf (fun n=>energy d a (u (s n))) atTop := by
    calc
      _ = ∫⁻k,liminf (fun n=>‖difference (u (s n)) k‖ₑ^2) atTop ∂weightedCoarea d a := by
        apply lintegral_congr_ae
        exact hd.mono (fun _ hk=>hk.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun n=>
        (difference_aestronglyMeasurable hd0 hdU a (u (s n))).enorm.pow_const 2)
  have hl0 : liminf (fun n=>energy d a (u (s n))) atTop=0 := by
    simpa only [Function.comp_def] using (henergy.comp hs.tendsto_atTop).liminf_eq
  rw [hl0] at hlim
  have hz : energy d a f=0 := le_antisymm hlim (zero_le _)
  have hzero := (lintegral_eq_zero_iff'
    ((difference_aestronglyMeasurable hd0 hdU a f).enorm.pow_const 2)).mp hz
  change (0:Target d a)=ᵐ[weightedCoarea d a] difference f
  filter_upwards [hzero,Lp.coeFn_zero ℂ 2 (weightedCoarea d a)] with k hk h0
  have hn : ‖difference f k‖ₑ=0 := eq_zero_of_pow_eq_zero hk
  exact h0.trans (enorm_eq_zero.mp hn).symm

/-- A positive lower bound on the original orthogonal unit sphere. -/
theorem orthogonal_unit_gap {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (ha:Continuous a) (hpos:∀k,0<a k) :
    ∃γ:ℝ,0<γ ∧ ∀f:Source,f∈(nullSpace hd0 hdU a)ᗮ→‖f‖=1→
      ENNReal.ofReal γ≤energy d a f := by
  by_contra hn
  push Not at hn
  have hchoice (n:ℕ) : ∃f:Source,f∈(nullSpace hd0 hdU a)ᗮ ∧ ‖f‖=1 ∧
      energy d a f<ENNReal.ofReal (1/((n:ℝ)+1)) :=
    hn (1/((n:ℝ)+1)) (by positivity)
  choose u hu hnorm hsmall using hchoice
  have hlim : Tendsto (fun n:ℕ=>ENNReal.ofReal (1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n:ℕ=>1/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)))
  have henergy : Tendsto (fun n=>energy d a (u n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _=>zero_le _) (fun n=>(hsmall n).le)
  have hbound (n:ℕ) : eLpNorm (u n) 2 circleHaar≤1 := by
    rw [←Lp.enorm_def,←ofReal_norm,hnorm n]
    simp
  obtain ⟨f,s,hs,hconv⟩ := PinnedWeightedCompactness.weighted_near_kernel_L2_subsequence
    hd0 hdU a ha hpos u (R:=1) (by norm_num) hbound henergy
  have hforth : f∈(nullSpace hd0 hdU a)ᗮ :=
    (nullSpace hd0 hdU a).isClosed_orthogonal.mem_of_tendsto hconv
      (Eventually.of_forall (fun n=>hu (s n)))
  have hfnull : f∈nullSpace hd0 hdU a :=
    nullSpace_of_tendsto_energy_zero hd0 hdU a hconv (henergy.comp hs.tendsto_atTop)
  have hfzero : f=0 := by
    have hh : f∈nullSpace hd0 hdU a ⊓ (nullSpace hd0 hdU a)ᗮ := ⟨hfnull,hforth⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hh
    exact hh
  have hfnorm : ‖f‖=1 := tendsto_nhds_unique hconv.norm
    (by simpa only [Function.comp_def,hnorm] using
      (tendsto_const_nhds : Tendsto (fun _n:ℕ=>(1:ℝ)) atTop (𝓝 1)))
  simp [hfzero] at hfnorm

/-- Homogeneity of the complete difference, including infinite energies. -/
theorem energy_smul {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (c:ℂ) (f:Source) :
    energy d a (c • f)=‖c‖ₑ^2*energy d a f := by
  have hd := difference_ae_congr hd0 hdU a (Lp.coeFn_smul c f)
  calc
    _ = ∫⁻k,‖c‖ₑ^2*‖difference f k‖ₑ^2 ∂weightedCoarea d a := by
      apply lintegral_congr_ae
      filter_upwards [hd] with k hk
      have he : difference ((c • f : Source):PinnedPeriodicity.Circle→ℂ) k=c*difference f k := by
        rw [hk]
        simp only [difference,Pi.smul_apply,smul_eq_mul]
        ring
      rw [he,enorm_mul,mul_pow]
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

set_option maxHeartbeats 800000 in
/-- The lower bound is homogeneous and applies to every orthogonal vector,
without imposing finite energy as a premise. -/
theorem orthogonal_gap {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (ha:Continuous a) (hpos:∀k,0<a k) :
    ∃γ:ℝ,0<γ ∧ ∀f:Source,f∈(nullSpace hd0 hdU a)ᗮ→
      ENNReal.ofReal γ*‖f‖ₑ^2≤energy d a f := by
  obtain ⟨γ,hγ,hunit⟩ := orthogonal_unit_gap hd0 hdU a ha hpos
  refine ⟨γ,hγ,?_⟩
  intro f hf
  by_cases hz:f=0
  · simp [hz]
  have hn : ‖f‖≠0 := norm_ne_zero_iff.mpr hz
  have hc : (‖f‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  let v : Source := (‖f‖:ℂ)⁻¹ • f
  have hv : v∈(nullSpace hd0 hdU a)ᗮ := (nullSpace hd0 hdU a)ᗮ.smul_mem _ hf
  have hvnorm : ‖v‖=1 := by
    simp [v,norm_smul,norm_inv,Complex.norm_real,hn]
  have hrepr : (‖f‖:ℂ) • v=f := by
    simp [v,smul_smul,hc]
  have hcoeff : ‖(‖f‖:ℂ)‖ₑ=‖f‖ₑ := by
    rw [←ofReal_norm,Complex.norm_real,norm_norm,ofReal_norm]
  calc
    ENNReal.ofReal γ*‖f‖ₑ^2 = ‖(‖f‖:ℂ)‖ₑ^2*ENNReal.ofReal γ := by rw [hcoeff,mul_comm]
    _ ≤ ‖(‖f‖:ℂ)‖ₑ^2*energy d a v := mul_le_mul_right (hunit v hv hvnorm) _
    _ = energy d a ((‖f‖:ℂ) • v) := (energy_smul hd0 hdU a _ v).symm
    _ = energy d a f := by rw [hrepr]

theorem energy_sub_nullSpace {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (f p:Source) (hp:p∈nullSpace hd0 hdU a) :
    energy d a (f-p)=energy d a f := by
  have hdiff : ∀ᵐk∂weightedCoarea d a,difference p k=0 := by
    change (0:Target d a)=ᵐ[weightedCoarea d a] difference p at hp
    filter_upwards [hp,Lp.coeFn_zero ℂ 2 (weightedCoarea d a)] with k hk h0
    exact hk.symm.trans h0
  have hsub := difference_ae_congr hd0 hdU a (Lp.coeFn_sub f p)
  apply lintegral_congr_ae
  filter_upwards [hdiff,hsub] with k hp hs
  have he : difference ((f-p : Source):PinnedPeriodicity.Circle→ℂ) k=difference f k-difference p k := by
    rw [hs]
    simp only [difference,Pi.sub_apply]
    ring
  rw [he,hp,sub_zero]

/-- The nullspace, hence its orthogonal projection, is the same original
two-mode space for every continuous strictly positive quartet weight. -/
theorem nullSpace_weight_independent {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a b:FourCircle→ℝ) (ha:Continuous a) (hpa:∀k,0<a k)
    (hb:Continuous b) (hpb:∀k,0<b k) :
    nullSpace hd0 hdU a=nullSpace hd0 hdU b := by
  ext f
  rw [nullSpace_classification hd0 hdU a ha hpa,
    nullSpace_classification hd0 hdU b hb hpb]

/-- The paper's positive gap for the maximal original full-coarea form.
The projection is derived from the actual closed kernel, whose exact
range is identified by `nullSpace_classification`.  Infinite energy is
allowed, so this statement covers the whole physical L² space. -/
theorem full_coarea_spectral_gap {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    (a:FourCircle→ℝ) (ha:Continuous a) (hpos:∀k,0<a k) :
    ∃γ:ℝ,0<γ ∧ ∀f:Source,
      ENNReal.ofReal γ*‖f-(nullSpace hd0 hdU a).starProjection f‖ₑ^2≤energy d a f := by
  obtain ⟨γ,hγ,hgap⟩ := orthogonal_gap hd0 hdU a ha hpos
  refine ⟨γ,hγ,fun f=>?_⟩
  have h := hgap (f-(nullSpace hd0 hdU a).starProjection f)
    ((nullSpace hd0 hdU a).sub_starProjection_mem_orthogonal f)
  rwa [energy_sub_nullSpace hd0 hdU a f _
    ((nullSpace hd0 hdU a).starProjection_apply_mem f)] at h

/-- The exact weight comparison uses the same complete coarea and needs
no symmetry of the quartet weight. -/
theorem energy_weight_lower_bound (d:ℝ) (a:FourCircle→ℝ) (b:ℝ)
    (hlower:∀k,b≤a k) (f:Source) :
    ENNReal.ofReal b*energy d (fun _=>1) f≤energy d a f := by
  have hm : ENNReal.ofReal b • weightedCoarea d (fun _=>1)≤weightedCoarea d a := by
    have h := withDensity_mono (μ:=euclideanCircleRegularCoarea d)
      (Eventually.of_forall (fun k=>ENNReal.ofReal_le_ofReal (hlower (fullLegs k))))
    change ENNReal.ofReal b • (euclideanCircleRegularCoarea d).withDensity (fun _=>ENNReal.ofReal 1)≤
      (euclideanCircleRegularCoarea d).withDensity (fun k=>ENNReal.ofReal (a (fullLegs k)))
    rw [ENNReal.ofReal_one,withDensity_const,one_smul]
    simpa only [withDensity_const] using h
  calc
    _ = ∫⁻k,‖difference f k‖ₑ^2 ∂(ENNReal.ofReal b • weightedCoarea d (fun _=>1)) :=
      (lintegral_smul_measure _ _).symm
    _ ≤ _ := lintegral_mono' hm (le_refl _)

/-- A single dispersion-dependent gap works uniformly over every family
of quartet weights sharing the displayed positive lower bound. -/
theorem uniform_lower_weight_spectral_gap {d:ℝ} (hd0:0<d) (hdU:d<1/2) :
    ∃γ:ℝ,0<γ ∧ ∀(a:FourCircle→ℝ) (b:ℝ),0<b→(∀k,b≤a k)→∀f:Source,
      ENNReal.ofReal (b*γ)*‖f-(nullSpace hd0 hdU (fun _=>1)).starProjection f‖ₑ^2
        ≤energy d a f := by
  obtain ⟨γ,hγ,hgap⟩ := full_coarea_spectral_gap hd0 hdU (fun _=>1)
    continuous_const (fun _=>by norm_num)
  refine ⟨γ,hγ,fun a b hb hlower f=>?_⟩
  calc
    _ = ENNReal.ofReal b*(ENNReal.ofReal γ*
        ‖f-(nullSpace hd0 hdU (fun _=>1)).starProjection f‖ₑ^2) := by
      rw [ENNReal.ofReal_mul hb.le,mul_assoc]
    _ ≤ ENNReal.ofReal b*energy d (fun _=>1) f := mul_le_mul_right (hgap f) _
    _ ≤ energy d a f := energy_weight_lower_bound d a b hlower f

end
end Resonance.PinnedGap
