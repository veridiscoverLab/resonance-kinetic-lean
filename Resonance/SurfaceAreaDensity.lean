import Resonance.SurfaceMetricComparison
import Resonance.LinearSurfaceArea
import Resonance.MeasureLocalComparison
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Exact surface measure from the strict derivative. Local comparisons concern
the original normalized Hausdorff measure, and are glued before the distortion
is sent to one. -/
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology EuclideanGeometry
namespace Resonance.SurfaceAreaDensity
noncomputable section
open LinearSurfaceArea SurfaceMetricComparison MeasureLocalComparison

def surfaceMeasure (f:P→A) : Measure P := (μHE[2]:Measure A).comap f
def densityMeasure (J:P→ℝ) : Measure P := volume.withDensity (fun x=>ENNReal.ofReal (J x))

theorem local_density_sandwich (f:P→A) (hf:MeasurableEmbedding f)
    (L:P→L[ℝ]A) (hL:Function.Injective L) (U:Set P) (hU:MeasurableSet U)
    (J:P→ℝ) (hJ:Measurable J) (K:ℝ≥0)
    (hmetric:∀x∈U,∀y∈U,dist (f x) (f y)≤K*dist (L x) (L y))
    (hmetric':∀x∈U,∀y∈U,dist (L x) (L y)≤K*dist (f x) (f y))
    (hlo:∀x∈U,gramJacobian L≤K*J x)
    (hhi:∀x∈U,J x≤K*gramJacobian L) :
    (surfaceMeasure f).restrict U≤(K:ℝ≥0∞)^3 • (densityMeasure J).restrict U ∧
    (densityMeasure J).restrict U≤(K:ℝ≥0∞)^3 • (surfaceMeasure f).restrict U := by
  have hlocal:∀s,MeasurableSet s→
      (μHE[2]:Measure A) (f '' (s∩U))≤(K:ℝ≥0∞)^3*∫⁻x in s∩U,ENNReal.ofReal (J x) ∧
      (∫⁻x in s∩U,ENNReal.ofReal (J x))≤(K:ℝ≥0∞)^3*(μHE[2]:Measure A) (f '' (s∩U)):=by
    intro s hs
    have ht:=hs.inter hU
    have ha:=normalized_area_image_comparison f L hL (s∩U) K
      (fun x hx y hy=>hmetric x hx.2 y hy.2) 2
    have hb:=normalized_area_image_comparison L f hf.injective (s∩U) K
      (fun x hx y hy=>hmetric' x hx.2 y hy.2) 2
    rw [linear_image_area hL] at ha hb
    have hlow:ENNReal.ofReal (gramJacobian L)*volume (s∩U)≤
        (K:ℝ≥0∞)*(∫⁻x in s∩U,ENNReal.ofReal (J x)):=by
      have h:=lintegral_mono_ae (μ:=volume.restrict (s∩U)) (f:=fun _=>ENNReal.ofReal (gramJacobian L))
        (g:=fun x=>(K:ℝ≥0∞)*ENNReal.ofReal (J x)) ?_
      · simpa only [lintegral_const,Measure.restrict_apply_univ,
          lintegral_const_mul _ hJ.ennreal_ofReal] using h
      · filter_upwards [ae_restrict_mem ht] with x hx
        simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg K),ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal (hlo x hx.2)
    have hhigh:(∫⁻x in s∩U,ENNReal.ofReal (J x))≤
        (K:ℝ≥0∞)*ENNReal.ofReal (gramJacobian L)*volume (s∩U):=by
      have h:=lintegral_mono_ae (μ:=volume.restrict (s∩U)) (f:=fun x=>ENNReal.ofReal (J x))
        (g:=fun _=>(K:ℝ≥0∞)*ENNReal.ofReal (gramJacobian L)) ?_
      · simpa only [lintegral_const,Measure.restrict_apply_univ] using h
      · filter_upwards [ae_restrict_mem ht] with x hx
        simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg K),ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal (hhi x hx.2)
    constructor
    · calc
        _ ≤ (K:ℝ≥0∞)^2*(ENNReal.ofReal (gramJacobian L)*volume (s∩U)):=ha
        _ ≤ (K:ℝ≥0∞)^2*((K:ℝ≥0∞)*(∫⁻x in s∩U,ENNReal.ofReal (J x))):=mul_le_mul_right hlow _
        _ = _:=by ring
    · calc
        _ ≤ (K:ℝ≥0∞)*(ENNReal.ofReal (gramJacobian L)*volume (s∩U)):=by simpa only [mul_assoc] using hhigh
        _ ≤ (K:ℝ≥0∞)*((K:ℝ≥0∞)^2*(μHE[2]:Measure A) (f '' (s∩U))):=mul_le_mul_right hb _
        _ = _:=by ring
  constructor <;> apply Measure.le_iff.mpr <;> intro s hs
  · simpa only [surfaceMeasure,densityMeasure,Measure.restrict_apply hs,
      Measure.comap_apply f hf.injective (fun t ht=>hf.measurableSet_image.mpr ht) _ (hs.inter hU),
      withDensity_apply _ (hs.inter hU),Measure.smul_apply,smul_eq_mul] using (hlocal s hs).1
  · simpa only [surfaceMeasure,densityMeasure,Measure.restrict_apply hs,
      Measure.comap_apply f hf.injective (fun t ht=>hf.measurableSet_image.mpr ht) _ (hs.inter hU),
      withDensity_apply _ (hs.inter hU),Measure.smul_apply,smul_eq_mul] using (hlocal s hs).2

theorem local_derivative_density_sandwich (f:P→A) (hf:MeasurableEmbedding f)
    (T:Set P) (hT:IsOpen T) (L:P→P→L[ℝ]A) (J:P→ℝ) (hJ:Measurable J)
    (hJc:ContinuousOn J T) {x:P} (hx:x∈T)
    (hdf:HasStrictFDerivAt f (L x) x) (hL:∀v,‖v‖≤‖L x v‖)
    (hJeq:J x=gramJacobian (L x)) (hJpos:0<J x)
    {ε:ℝ} (hε:0<ε) (hε1:ε<1) :
    ∃V:Set P,IsOpen V∧x∈V∧V⊆T∧
      (surfaceMeasure f).restrict V≤ENNReal.ofReal ((1+ε)^3) • (densityMeasure J).restrict V ∧
      (densityMeasure J).restrict V≤ENNReal.ofReal ((1+ε)^3) • (surfaceMeasure f).restrict V := by
  have hK:0<1+ε:=by linarith
  obtain ⟨U,hU,hxU,hmet,hmet'⟩:=strict_derivative_metric_comparison hdf hL
    (ε:=ε/2) (by positivity) (by linarith)
  have hlo:J x/(1+ε)<J x:=by
    apply (div_lt_iff₀ hK).mpr
    nlinarith
  have hhi:J x<(1+ε)*J x:=by nlinarith
  have hJn:{y|J x/(1+ε)<J y∧J y<(1+ε)*J x}∈𝓝 x:=
    (hJc.continuousAt (hT.mem_nhds hx)).eventually (Ioo_mem_nhds hlo hhi)
  obtain ⟨W,hWsub,hW,hxW⟩:=mem_nhds_iff.mp hJn
  let V:=U∩W∩T
  have hV:IsOpen V:=(hU.inter hW).inter hT
  have hVsub:V⊆T:=fun _ h=>h.2
  have hLi:Function.Injective (L x):=by
    intro y z hyz
    have h:=hL (y-z)
    rw [map_sub,hyz,sub_self,norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hKinv:(1-ε/2)⁻¹≤1+ε:=by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith:0<1-ε/2)).mpr
    nlinarith
  have h:=local_density_sandwich f hf (L x) hLi V hV.measurableSet J hJ
    ⟨1+ε,hK.le⟩ ?_ ?_ ?_ ?_
  · refine ⟨V,hV,⟨⟨hxU,hxW⟩,hx⟩,hVsub,?_⟩
    simpa only [ENNReal.ofReal_pow hK.le,ENNReal.ofReal_eq_coe_nnreal hK.le] using h
  · intro y hy z hz
    exact (hmet y hy.1.1 z hz.1.1).trans
      (mul_le_mul_of_nonneg_right (show 1+ε/2≤1+ε by linarith) dist_nonneg)
  · intro y hy z hz
    exact (hmet' y hy.1.1 z hz.1.1).trans
      (mul_le_mul_of_nonneg_right hKinv dist_nonneg)
  · intro y hy
    have hh: J x/(1+ε)<J y:=(hWsub hy.1.2).1
    rw [div_lt_iff₀ hK] at hh
    simpa only [←hJeq,mul_comm] using hh.le
  · intro y hy
    simpa only [←hJeq] using (hWsub hy.1.2).2.le

theorem surfaceMeasure_eq_density_on (f:P→A) (hf:MeasurableEmbedding f)
    (T:Set P) (hT:IsOpen T) (L:P→P→L[ℝ]A) (J:P→ℝ) (hJ:Measurable J)
    (hJc:ContinuousOn J T)
    (hdf:∀x∈T,HasStrictFDerivAt f (L x) x)
    (hL:∀x∈T,∀v,‖v‖≤‖L x v‖)
    (hJeq:∀x∈T,J x=gramJacobian (L x)) (hJpos:∀x∈T,0<J x) :
    (surfaceMeasure f).restrict T=(densityMeasure J).restrict T := by
  have hb:∀ε:ℝ,0<ε→ε<1→
      (surfaceMeasure f).restrict T≤ENNReal.ofReal ((1+ε)^3) • (densityMeasure J).restrict T ∧
      (densityMeasure J).restrict T≤ENNReal.ofReal ((1+ε)^3) • (surfaceMeasure f).restrict T:=by
    intro ε hε hε1
    have hloc:=fun x hx=>local_derivative_density_sandwich f hf T hT L J hJ hJc hx
      (hdf x hx) (hL x hx) (hJeq x hx) (hJpos x hx) hε hε1
    constructor
    · have h:=restrict_le_of_locally_restrict_le (surfaceMeasure f)
        (ENNReal.ofReal ((1+ε)^3) • densityMeasure J) T ?_
      · simpa only [Measure.restrict_smul] using h
      · intro x hx
        obtain ⟨V,hV,hxV,hsub,hlo,_⟩:=hloc x hx
        exact ⟨V,hV,hxV,hsub,by simpa only [Measure.restrict_smul] using hlo⟩
    · have h:=restrict_le_of_locally_restrict_le (densityMeasure J)
        (ENNReal.ofReal ((1+ε)^3) • surfaceMeasure f) T ?_
      · simpa only [Measure.restrict_smul] using h
      · intro x hx
        obtain ⟨V,hV,hxV,hsub,_,hhi⟩:=hloc x hx
        exact ⟨V,hV,hxV,hsub,by simpa only [Measure.restrict_smul] using hhi⟩
  have ht:Tendsto (fun ε:ℝ=>ENNReal.ofReal ((1+ε)^3)) (𝓝[>] 0) (𝓝 1):=by
    have h:ContinuousAt (fun ε:ℝ=>ENNReal.ofReal ((1+ε)^3)) 0:=
      ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall:∀ᶠε:ℝ in 𝓝[>]0,0<ε∧ε<1:=by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num: (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds]
      with ε hε hε1
    exact ⟨hε,hε1⟩
  apply le_antisymm <;> apply Measure.le_iff.mpr <;> intro s _hs
  · have hlim:=ENNReal.Tendsto.mul_const ht (b:=((densityMeasure J).restrict T) s) (Or.inl one_ne_zero)
    simp only [one_mul] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [hsmall] with ε hε
    exact (hb ε hε.1 hε.2).1 s
  · have hlim:=ENNReal.Tendsto.mul_const ht (b:=((surfaceMeasure f).restrict T) s) (Or.inl one_ne_zero)
    simp only [one_mul] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [hsmall] with ε hε
    exact (hb ε hε.1 hε.2).2 s

end
end Resonance.SurfaceAreaDensity
