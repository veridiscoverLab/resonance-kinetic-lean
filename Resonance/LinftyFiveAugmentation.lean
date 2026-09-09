import Resonance.LinftyPhysicalForm
import Resonance.PhysicalProjectionKernel
import Mathlib.Analysis.Normed.Operator.FredholmAlternative

/-! Actual five-moment finite-rank augmentation of the original bounded
integral operator. The added term is derived from N times the five original
invariants, and its kernel is eliminated using the complete collision form. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.LinftyFiveAugmentation
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity ReferenceMomentFunctionals
open LinftyPhysicalDomain LinftyPhysicalForm

def continuousBasis {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    C(cube R,ℝ) := ⟨fun k=>basisFunction θ i k,(basis_continuousOn hθ i).restrict⟩

def synthesisContinuous {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Parameter→L[ℝ]C(cube R,ℝ) :=
  ∑i : Fin 5,(ContinuousLinearMap.proj i).smulRight (continuousBasis hθ i)

theorem synthesisContinuous_apply {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    (b : Parameter) (k : cube R) :
    synthesisContinuous hθ b k=∑i : Fin 5,b i*basisFunction θ i k := by
  simp [synthesisContinuous,continuousBasis]

def synthesisTop {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Parameter→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (CubeLinftyCoordinates.embed R).comp (synthesisContinuous hθ)

theorem synthesisTop_ae {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (b : Parameter) :
    synthesisTop hθ b=ᵐ[cubeVolume R] (fun k=>∑i : Fin 5,b i*basisFunction θ i k) := by
  filter_upwards [CubeLinftyCoordinates.embed_ae R (synthesisContinuous hθ b),
    ae_restrict_mem (measurable_cube R)] with k he hk
  exact he.trans ((CubeLinftyCoordinates.zeroExtension_apply R
    (synthesisContinuous hθ b) ⟨k,hk⟩).trans (synthesisContinuous_apply hθ b ⟨k,hk⟩))

theorem synthesisTop_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) (b : Parameter) :
    (∫k,u k*(synthesisTop hθ b) k∂cubeVolume R)=
      ∑i : Fin 5,b i*(analysisMap hR hθ u) i := by
  calc
    _ = ∫k,∑i : Fin 5,b i*(u k*basisFunction θ i k)∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [synthesisTop_ae hθ b] with k hk
      rw [hk,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [integral_finset_sum Finset.univ
        (fun i _=>(weighted_moment_integrable hR (basis_memLp_top hθ i) u).const_mul (b i))]
      simp only [integral_const_mul,analysisMap_apply]

def correction {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (synthesisTop hθ).comp ((analysisMap hR hθ).comp (divide hR hθ))

theorem correction_compact {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : IsCompactOperator (correction hR hθ) := by
  have hs : IsCompactOperator (synthesisTop hθ) :=
    isCompactOperator_of_locallyCompactSpace_rng (synthesisTop hθ)
  exact hs.comp_clm ((analysisMap hR hθ).comp (divide hR hθ))

def compactPart {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  AmbientLinftyCompact.operator hR hθ+correction hR hθ

theorem compactPart_compact {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : IsCompactOperator (compactPart hR hθ) :=
  (AmbientLinftyCompact.operator_compact hR hθ).add (correction_compact hR hθ)

def augmented {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) := 1+compactPart hR hθ

theorem augmented_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : Lp ℝ ∞ (cubeVolume R)) (v : Space R) :
    (∫k,v k*(augmented hR hθ f) k∂cubeVolume R)=
      physicalForm hR.le hθ (divide hR hθ f) v+
        ∑i : Fin 5,(analysisMap hR hθ (divide hR hθ f)) i*(analysisMap hR hθ v) i := by
  have he : (fun k=>v k*(augmented hR hθ f) k)=ᵐ[cubeVolume R]
      (fun k=>v k*(f k+(AmbientLinftyCompact.operator hR hθ f) k)+
        v k*(correction hR hθ f) k) := by
    filter_upwards [Lp.coeFn_add f (compactPart hR hθ f),
      Lp.coeFn_add (AmbientLinftyCompact.operator hR hθ f) (correction hR hθ f)] with k h1 h2
    change v k*(f+compactPart hR hθ f) k=_
    change (f+compactPart hR hθ f) k=f k+(compactPart hR hθ f) k at h1
    change (compactPart hR hθ f) k=(AmbientLinftyCompact.operator hR hθ f) k+
      (correction hR hθ f) k at h2
    rw [h1,h2]
    ring
  have hc : Integrable (fun k=>v k*(correction hR hθ f) k) (cubeVolume R) := by
    apply (divided_diagonal hR hθ (correction hR hθ f) v).1.congr
    exact ae_of_all _ (fun _=>mul_comm _ _)
  rw [integral_congr_ae he,integral_add (actual_form_identity hR hθ f v).1 hc,
    ←(actual_form_identity hR hθ f v).2]
  congr 1
  exact synthesisTop_pairing hR hθ v (analysisMap hR hθ (divide hR hθ f))

theorem augmented_kernel_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {f : Lp ℝ ∞ (cubeVolume R)}
    (hf : augmented hR hθ f=0) : f=0 := by
  let u := divide hR hθ f
  let a := analysisMap hR hθ u
  have he := augmented_pairing hR hθ f u
  rw [hf] at he
  have hz : (∫k,u k*(0 : Lp ℝ ∞ (cubeVolume R)) k∂cubeVolume R)=0 := by
    calc
      _ = ∫k,(0:ℝ)∂cubeVolume R := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero ℝ ∞ (cubeVolume R)] with k hk
        simp only [hk,Pi.zero_apply,mul_zero]
      _ = 0 := integral_zero _ _
  rw [hz,physical_form_square] at he
  have hs : 0≤∑i : Fin 5,a i*a i := Finset.sum_nonneg (fun i _=>mul_self_nonneg (a i))
  have hd : physicalDifference hR.le hθ u=0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (physicalDifference hR.le hθ u)]
  have haz : a=0 := by
    have hh : ∑i : Fin 5,a i*a i=0 := by nlinarith [sq_nonneg ‖physicalDifference hR.le hθ u‖]
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>mul_self_nonneg (a i))).mp hh i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hi
  have hu : u=0 := by
    rw [←projection_fixed_kernel hR hθ hd]
    change synthesis hR.le hθ (gramInverse hR hθ a)=0
    rw [haz,map_zero,map_zero]
  apply divide_injective hR hθ
  simpa only [map_zero] using hu

theorem augmented_injective {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Function.Injective (augmented hR hθ) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply augmented_kernel_zero hR hθ
  rw [map_sub,hfg,sub_self]

theorem augmented_bijective {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Function.Bijective (augmented hR hθ) := by
  have hn : ¬Module.End.HasEigenvalue (compactPart hR hθ).toLinearMap (-1) := by
    rw [Module.End.hasEigenvalue_iff,not_not]
    apply le_antisymm ?_ bot_le
    intro f hf
    change f=0
    apply augmented_kernel_zero hR hθ
    have he := Module.End.mem_eigenspace_iff.mp hf
    change compactPart hR hθ f=(-1 : ℝ) • f at he
    change f+compactPart hR hθ f=0
    rw [he,neg_one_smul,add_neg_cancel]
  have hr := ((compactPart_compact hR hθ).hasEigenvalue_or_mem_resolventSet
    (by norm_num : (-1 : ℝ)≠0)).resolve_left hn
  rw [spectrum.mem_resolventSet_iff] at hr
  have he : algebraMap ℝ (Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R)) (-1)-
      compactPart hR hθ= -(augmented hR hθ) := by
    apply ContinuousLinearMap.ext
    intro f
    change (-1 : ℝ) • f-compactPart hR hθ f= -(f+compactPart hR hθ f)
    rw [neg_one_smul]
    abel
  rw [he,IsUnit.neg_iff,ContinuousLinearMap.isUnit_iff_bijective] at hr
  exact hr

def augmentedEquiv {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R)≃L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  ContinuousLinearEquiv.ofBijective (augmented hR hθ)
    (LinearMap.ker_eq_bot.mpr (augmented_bijective hR hθ).1)
    (LinearMap.range_eq_top.mpr (augmented_bijective hR hθ).2)

theorem augmentedEquiv_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : Lp ℝ ∞ (cubeVolume R)) :
    augmentedEquiv hR hθ f=augmented hR hθ f := rfl

theorem augmented_inverse_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : Lp ℝ ∞ (cubeVolume R)) :
    ‖(augmentedEquiv hR hθ).symm f‖≤
      ‖(augmentedEquiv hR hθ).symm.toContinuousLinearMap‖*‖f‖ :=
  (augmentedEquiv hR hθ).symm.toContinuousLinearMap.le_opNorm f

end
end Resonance.LinftyFiveAugmentation
