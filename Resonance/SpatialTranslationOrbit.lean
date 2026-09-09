import Resonance.SpatialJetDescent
import Resonance.UniformEvaluationDerivative
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The common spatial translation orbit of an actual compatible jet.  The
supremum-norm derivative is proved before applying free transport. -/
open Set Function Filter
open scoped Topology ContDiff
namespace Resonance.SpatialTranslationOrbit
noncomputable section
open FreeTransport SpatialChainRule SpatialJetSpace SpatialJetDescent
set_option maxHeartbeats 800000

section SectionOperator
variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K] [CompactSpace K]

local instance sectionNorm : Norm (C(K,E →L[ℝ] F) →L[ℝ] (E →L[ℝ] C(K,F))) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K,E →L[ℝ] F)) (F := E →L[ℝ] C(K,F)) (σ₁₂ := RingHom.id ℝ)

def sectionLinear (g : C(K,E →L[ℝ] F)) : E →ₗ[ℝ] C(K,F) where
  toFun h := ⟨fun k => g k h,g.continuous.clm_apply continuous_const⟩
  map_add' a b := by ext k; exact (g k).map_add a b
  map_smul' s a := by ext k; exact (g k).map_smul s a

theorem sectionLinear_bound (g : C(K,E →L[ℝ] F)) (h : E) :
    ‖sectionLinear g h‖≤‖g‖*‖h‖ := by
  apply (ContinuousMap.norm_le (sectionLinear g h) (mul_nonneg (norm_nonneg g) (norm_nonneg h))).mpr
  intro k
  exact ((g k).le_opNorm h).trans (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm k) (norm_nonneg h))

def sectionCLM (g : C(K,E →L[ℝ] F)) : E →L[ℝ] C(K,F) :=
  (sectionLinear g).mkContinuous ‖g‖ (sectionLinear_bound g)

@[simp] theorem sectionCLM_apply (g : C(K,E →L[ℝ] F)) (h : E) (k : K) :
    sectionCLM g h k=g k h := rfl

theorem sectionCLM_norm_le (g : C(K,E →L[ℝ] F)) : ‖sectionCLM g‖≤‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound (sectionCLM g) (norm_nonneg g) (sectionLinear_bound g)

def sectionMap : C(K,E →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] C(K,F)) where
  toFun := sectionCLM
  map_add' a b := by apply ContinuousLinearMap.ext; intro h; ext k; rfl
  map_smul' s a := by apply ContinuousLinearMap.ext; intro h; ext k; rfl

def sectionOperator : C(K,E →L[ℝ] F) →L[ℝ] (E →L[ℝ] C(K,F)) := by
  let L : C(K,E →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] C(K,F)) := sectionMap
  have hb (g : C(K,E →L[ℝ] F)) : ‖L g‖≤1*‖g‖ := by
    change ‖sectionCLM g‖≤1*‖g‖
    simpa only [one_mul] using sectionCLM_norm_le g
  exact LinearMap.mkContinuous (E := C(K,E →L[ℝ] F)) (F := E →L[ℝ] C(K,F)) L 1 hb

@[simp] theorem sectionOperator_apply (g : C(K,E →L[ℝ] F)) (h : E) (k : K) :
    sectionOperator (E := E) (F := F) (K := K) g h k=g k h := rfl

theorem sectionOperator_norm_le : ‖sectionOperator (E := E) (F := F) (K := K)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa only [one_mul] using sectionCLM_norm_le g

end SectionOperator

section Translation
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def translateField (f : C(SpatialTorus,F)) (x : RealPosition) : C(SpatialTorus,F) :=
  f.comp ⟨fun X : SpatialTorus => torusQuotient x+X,by fun_prop⟩

omit [NormedSpace ℝ F] in
@[simp] theorem translateField_apply (f : C(SpatialTorus,F)) (x : RealPosition) (X : SpatialTorus) :
    translateField f x X=f (torusQuotient x+X) := rfl

omit [NormedSpace ℝ F] in
theorem translateField_continuous (f : C(SpatialTorus,F)) : Continuous (translateField f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp ((torusQuotient_continuous.comp continuous_fst).add continuous_snd)

omit [NormedSpace ℝ F] in
theorem translateField_norm_le (f : C(SpatialTorus,F)) (x : RealPosition) :
    ‖translateField f x‖≤‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun X => f.norm_coe_le_norm (torusQuotient x+X))

theorem translateField_hasFDerivAt {f : C(SpatialTorus,F)}
    {g : C(SpatialTorus,RealPosition →L[ℝ] F)} (hfg : (f,g)∈fieldDerivativeGraph)
    (x : RealPosition) :
    HasFDerivAt (translateField f)
      (sectionOperator (E := RealPosition) (F := F) (K := SpatialTorus) (translateField g x)) x := by
  apply UniformEvaluationDerivative.hasFDerivAt_of_evaluations
    (((sectionOperator (E := RealPosition) (F := F) (K := SpatialTorus)).continuous.comp
      (translateField_continuous g)).continuousAt)
  intro y X
  obtain ⟨z,rfl⟩ := torusQuotient_surjective X
  have hf := (hfg (y+z)).comp y ((hasFDerivAt_id y).add_const z)
  have he : (fun v => translateField f v (torusQuotient z))=
      fun v => fieldLift f (v+z) := by
    funext v
    simp only [translateField_apply,fieldLift,Function.comp_apply,torusQuotient_add]
  rw [he]
  convert hf using 1

theorem translateField_contDiff_succ {f : C(SpatialTorus,F)}
    {g : C(SpatialTorus,RealPosition →L[ℝ] F)} (hfg : (f,g)∈fieldDerivativeGraph)
    {n : ℕ} (hg : ContDiff ℝ n (translateField g)) :
    ContDiff ℝ (n+1) (translateField f) := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨fun x => sectionOperator (E := RealPosition) (F := F) (K := SpatialTorus)
    (translateField g x),?_,translateField_hasFDerivAt hfg⟩
  exact (sectionOperator (E := RealPosition) (F := F) (K := SpatialTorus)).contDiff.comp hg

theorem norm_iterated_translateField_succ_le {f : C(SpatialTorus,F)}
    {g : C(SpatialTorus,RealPosition →L[ℝ] F)} (hfg : (f,g)∈fieldDerivativeGraph)
    {n : ℕ} (hg : ContDiff ℝ n (translateField g)) (x : RealPosition) :
    ‖iteratedFDeriv ℝ (n+1) (translateField f) x‖≤
      ‖iteratedFDeriv ℝ n (translateField g) x‖ := by
  have he : fderiv ℝ (translateField f)=
      sectionOperator (E := RealPosition) (F := F) (K := SpatialTorus) ∘ translateField g :=
    funext (fun y => (translateField_hasFDerivAt hfg y).fderiv)
  rw [← norm_iteratedFDeriv_fderiv,he]
  have hb := (sectionOperator (E := RealPosition) (F := F) (K := SpatialTorus)).norm_iteratedFDeriv_comp_left
    (f := translateField g) (x := x) (n := n) (N := (n : WithTop ℕ∞)) hg.contDiffAt le_rfl
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_right
    (sectionOperator_norm_le (E := RealPosition) (F := F) (K := SpatialTorus))
    (norm_nonneg (iteratedFDeriv ℝ n (translateField g) x))
  simpa only [one_mul] using hm

theorem compatible_translation_contDiff {R : ℝ} (p : SpatialJetSpace.JetSpace R) :
    ContDiff ℝ 3 (translateField p.1.1) := by
  have h3 : ContDiff ℝ 0 (translateField p.1.2.2.2) :=
    contDiff_zero.mpr (translateField_continuous _)
  have h2 := translateField_contDiff_succ p.2.2.2 h3
  have h1 := translateField_contDiff_succ p.2.2.1 h2
  exact translateField_contDiff_succ p.2.1 h1

theorem compatible_translation_derivative_norm {R : ℝ} (p : SpatialJetSpace.JetSpace R)
    (x : RealPosition) {n : ℕ} (hn : n≤3) :
    ‖iteratedFDeriv ℝ n (translateField p.1.1) x‖≤‖p‖ := by
  have h3 : ContDiff ℝ 0 (translateField p.1.2.2.2) :=
    contDiff_zero.mpr (translateField_continuous _)
  have h2 := translateField_contDiff_succ p.2.2.2 h3
  have h1 := translateField_contDiff_succ p.2.2.1 h2
  have b0 : ‖p.1.1‖≤‖p‖ := norm_fst_le p.1
  have b1 : ‖p.1.2.1‖≤‖p‖ := (norm_fst_le p.1.2).trans (norm_snd_le p.1)
  have b2 : ‖p.1.2.2.1‖≤‖p‖ := (norm_fst_le p.1.2.2).trans
    ((norm_snd_le p.1.2).trans (norm_snd_le p.1))
  have b3 : ‖p.1.2.2.2‖≤‖p‖ := (norm_snd_le p.1.2.2).trans
    ((norm_snd_le p.1.2).trans (norm_snd_le p.1))
  interval_cases n
  · simpa only [norm_iteratedFDeriv_zero] using (translateField_norm_le p.1.1 x).trans b0
  · exact (norm_iterated_translateField_succ_le p.2.1 (h1.of_le (by norm_num : (0 : WithTop ℕ∞)≤2)) x).trans
      (by simpa only [norm_iteratedFDeriv_zero] using (translateField_norm_le p.1.2.1 x).trans b1)
  · exact (norm_iterated_translateField_succ_le p.2.1 (h1.of_le (by norm_num : (1 : WithTop ℕ∞)≤2)) x).trans
      ((norm_iterated_translateField_succ_le p.2.2.1 (h2.of_le (by norm_num : (0 : WithTop ℕ∞)≤1)) x).trans
        (by simpa only [norm_iteratedFDeriv_zero] using (translateField_norm_le p.1.2.2.1 x).trans b2))
  · exact (norm_iterated_translateField_succ_le p.2.1 h1 x).trans
      ((norm_iterated_translateField_succ_le p.2.2.1 h2 x).trans
        ((norm_iterated_translateField_succ_le p.2.2.2 h3 x).trans
          (by simpa only [norm_iteratedFDeriv_zero] using (translateField_norm_le p.1.2.2.2 x).trans b3)))

end Translation

def uncurryLinear (R : ℝ) : C(SpatialTorus,V0 R) →ₗ[ℝ] Distribution R where
  toFun := ContinuousMap.uncurry
  map_add' a b := by ext p; rfl
  map_smul' s a := by ext p; rfl

theorem uncurryLinear_norm_le (R : ℝ) (f : C(SpatialTorus,V0 R)) :
    ‖uncurryLinear R f‖≤‖f‖ := by
  apply (ContinuousMap.norm_le (uncurryLinear R f) (norm_nonneg f)).mpr
  intro p
  exact ((f p.1).norm_coe_le_norm p.2).trans (f.norm_coe_le_norm p.1)

def uncurryCLM (R : ℝ) : C(SpatialTorus,V0 R) →L[ℝ] Distribution R :=
  (uncurryLinear R).mkContinuous 1 (fun f => by simpa only [one_mul] using uncurryLinear_norm_le R f)

theorem uncurryCLM_norm_le (R : ℝ) : ‖uncurryCLM R‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using uncurryLinear_norm_le R f

def zeroEvaluationLinear (R : ℝ) : Distribution R →ₗ[ℝ] V0 R where
  toFun f := f.curry 0
  map_add' a b := by ext k; rfl
  map_smul' s a := by ext k; rfl

def zeroEvaluationCLM (R : ℝ) : Distribution R →L[ℝ] V0 R :=
  (zeroEvaluationLinear R).mkContinuous 1 (fun f => by
    simpa only [one_mul] using SpatialCollision.momentumSection_norm_le f 0)

theorem zeroEvaluationCLM_norm_le (R : ℝ) : ‖zeroEvaluationCLM R‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using SpatialCollision.momentumSection_norm_le f 0

def distributionOrbit {R : ℝ} (f : Distribution R) (x : RealPosition) : Distribution R :=
  uncurryCLM R (translateField f.curry x)

@[simp] theorem distributionOrbit_apply {R : ℝ} (f : Distribution R) (x : RealPosition)
    (X : SpatialTorus) (k : MomentumDomain R) :
    distributionOrbit f x (X,k)=f (torusQuotient x+X,k) := rfl

theorem distributionOrbit_contDiff {R : ℝ} (p : SpatialJetSpace.JetSpace R) :
    ContDiff ℝ 3 (distributionOrbit (SpatialJetSpace.toDistribution p)) :=
  (uncurryCLM R).contDiff.comp (compatible_translation_contDiff p)

theorem distributionOrbit_derivative_norm {R : ℝ} (p : SpatialJetSpace.JetSpace R)
    (x : RealPosition) {n : ℕ} (hn : n≤3) :
    ‖iteratedFDeriv ℝ n (distributionOrbit (SpatialJetSpace.toDistribution p)) x‖≤‖p‖ := by
  exact ((uncurryCLM R).norm_iteratedFDeriv_comp_left
    (compatible_translation_contDiff p).contDiffAt (by exact_mod_cast hn)).trans
    ((mul_le_mul_of_nonneg_right (uncurryCLM_norm_le R) (norm_nonneg _)).trans
      (by simpa only [one_mul] using compatible_translation_derivative_norm p x hn))

theorem distributionOrbit_transport {R : ℝ} (t : ℝ) (f : Distribution R) (x : RealPosition) :
    distributionOrbit (transport R t f) x=transport R t (distributionOrbit f x) := by
  apply ContinuousMap.ext
  rintro ⟨X,k⟩
  change f (characteristic t (torusQuotient x+X,k))=
    f (torusQuotient x+(characteristic t (X,k)).1,(characteristic t (X,k)).2)
  congr 1
  apply Prod.ext
  · funext j
    simp only [characteristic,Pi.add_apply]
    abel
  · rfl

theorem realLift_transport_orbit {R : ℝ} (t : ℝ) (f : Distribution R) :
    realLift (transport R t f)=
      (zeroEvaluationCLM R) ∘ (transportCLM R t) ∘ distributionOrbit f := by
  funext x
  apply ContinuousMap.ext
  intro k
  change transport R t f (torusQuotient x,k)=transport R t (distributionOrbit f x) (0,k)
  rw [← distributionOrbit_transport]
  simp only [distributionOrbit_apply,add_zero]

/-- The same free characteristic preserves genuine spatial C³ regularity.
The collision variable k is only evaluated; it is never differentiated. -/
theorem transport_realLift_contDiff {R : ℝ} (t : ℝ) (p : SpatialJetSpace.JetSpace R) :
    ContDiff ℝ 3 (realLift (transport R t (SpatialJetSpace.toDistribution p))) := by
  rw [realLift_transport_orbit]
  exact (zeroEvaluationCLM R).contDiff.comp
    ((transportCLM R t).contDiff.comp (distributionOrbit_contDiff p))

end
end Resonance.SpatialTranslationOrbit

#check Resonance.SpatialTranslationOrbit.sectionLinear_bound
#check Resonance.SpatialTranslationOrbit.sectionCLM_apply
#check Resonance.SpatialTranslationOrbit.sectionCLM_norm_le
#check Resonance.SpatialTranslationOrbit.sectionOperator_apply
#check Resonance.SpatialTranslationOrbit.sectionOperator_norm_le
#check Resonance.SpatialTranslationOrbit.translateField_apply
#check Resonance.SpatialTranslationOrbit.translateField_continuous
#check Resonance.SpatialTranslationOrbit.translateField_norm_le
#check Resonance.SpatialTranslationOrbit.translateField_hasFDerivAt
#check Resonance.SpatialTranslationOrbit.translateField_contDiff_succ
#check Resonance.SpatialTranslationOrbit.norm_iterated_translateField_succ_le
#check Resonance.SpatialTranslationOrbit.compatible_translation_contDiff
#check Resonance.SpatialTranslationOrbit.compatible_translation_derivative_norm
#check Resonance.SpatialTranslationOrbit.uncurryLinear_norm_le
#check Resonance.SpatialTranslationOrbit.uncurryCLM_norm_le
#check Resonance.SpatialTranslationOrbit.zeroEvaluationCLM_norm_le
#check Resonance.SpatialTranslationOrbit.distributionOrbit_apply
#check Resonance.SpatialTranslationOrbit.distributionOrbit_contDiff
#check Resonance.SpatialTranslationOrbit.distributionOrbit_derivative_norm
#check Resonance.SpatialTranslationOrbit.distributionOrbit_transport
#check Resonance.SpatialTranslationOrbit.realLift_transport_orbit
#check Resonance.SpatialTranslationOrbit.transport_realLift_contDiff
#print axioms Resonance.SpatialTranslationOrbit.sectionLinear_bound
#print axioms Resonance.SpatialTranslationOrbit.sectionCLM_apply
#print axioms Resonance.SpatialTranslationOrbit.sectionCLM_norm_le
#print axioms Resonance.SpatialTranslationOrbit.sectionOperator_apply
#print axioms Resonance.SpatialTranslationOrbit.sectionOperator_norm_le
#print axioms Resonance.SpatialTranslationOrbit.translateField_apply
#print axioms Resonance.SpatialTranslationOrbit.translateField_continuous
#print axioms Resonance.SpatialTranslationOrbit.translateField_norm_le
#print axioms Resonance.SpatialTranslationOrbit.translateField_hasFDerivAt
#print axioms Resonance.SpatialTranslationOrbit.translateField_contDiff_succ
#print axioms Resonance.SpatialTranslationOrbit.norm_iterated_translateField_succ_le
#print axioms Resonance.SpatialTranslationOrbit.compatible_translation_contDiff
#print axioms Resonance.SpatialTranslationOrbit.compatible_translation_derivative_norm
#print axioms Resonance.SpatialTranslationOrbit.uncurryLinear_norm_le
#print axioms Resonance.SpatialTranslationOrbit.uncurryCLM_norm_le
#print axioms Resonance.SpatialTranslationOrbit.zeroEvaluationCLM_norm_le
#print axioms Resonance.SpatialTranslationOrbit.distributionOrbit_apply
#print axioms Resonance.SpatialTranslationOrbit.distributionOrbit_contDiff
#print axioms Resonance.SpatialTranslationOrbit.distributionOrbit_derivative_norm
#print axioms Resonance.SpatialTranslationOrbit.distributionOrbit_transport
#print axioms Resonance.SpatialTranslationOrbit.realLift_transport_orbit
#print axioms Resonance.SpatialTranslationOrbit.transport_realLift_contDiff
