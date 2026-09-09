import Resonance.ReferenceMomentFunctionals
import Resonance.ThermodynamicChart

/-! The manuscript's actual N times five invariants in its fixed weighted
Hilbert space, and the unweighted moment analysis and synthesis maps. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.PhysicalFiveBasis
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics
open CoareaNormalization (euclideanFive euclideanFive_continuous euclideanFive_coordinate
  thermodynamic_cube_integral toMomentumE)
open ActualPairNormalization ReferenceFrequencySpace ReferenceMomentFunctionals

theorem reference_finite {R : ℝ} (hR : 0≤R) : IsFiniteMeasure (referenceMeasure R) := by
  letI := jointMeasure_finite hR (JointWeightComparison.unitParameter_positive R)
  letI : IsFiniteMeasure (FrequencyWeightedForm.marginal R JointWeightComparison.unitParameter) := by
    unfold FrequencyWeightedForm.marginal
    infer_instance
  refine ⟨lt_of_le_of_lt (reference_le_unit hR univ) ?_⟩
  change upperFactor R*FrequencyWeightedForm.marginal R JointWeightComparison.unitParameter univ<∞
  exact ENNReal.mul_lt_top (upperFactor_finite R).lt_top (measure_lt_top _ _)

theorem continuous_cube_bounded {R : ℝ} {f : E→ℝ} (hf : ContinuousOn f (cube R)) :
    ∃C : ℝ,∀k∈cube R,‖f k‖≤C := by
  obtain ⟨C,hC⟩ := (FiberContinuity.cube_isCompact R).bddAbove_image hf.norm
  exact ⟨C,fun k hk=>hC ⟨k,hk,rfl⟩⟩

theorem continuous_cube_memLp_top {R : ℝ} {f : E→ℝ}
    (hm : Measurable f) (hc : ContinuousOn f (cube R)) :
    MemLp f ∞ (referenceMeasure R) := by
  obtain ⟨C,hC⟩ := continuous_cube_bounded hc
  apply memLp_top_of_bound hm.aestronglyMeasurable C
  filter_upwards [reference_support R] with k hk
  exact hC k hk

def basisFunction (θ : Parameter) (i : Fin 5) (k : E) : ℝ :=
  profile θ k*euclideanFive i k

theorem basis_measurable (θ : Parameter) (i : Fin 5) : Measurable (basisFunction θ i) :=
  (profile_measurable θ).mul (euclideanFive_continuous i).measurable

theorem basis_continuousOn {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    ContinuousOn (basisFunction θ i) (cube R) :=
  (FrequencyWeightedKernel.profile_continuousOn hθ).mul (euclideanFive_continuous i).continuousOn

theorem basis_memLp_top {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    MemLp (basisFunction θ i) ∞ (referenceMeasure R) :=
  continuous_cube_memLp_top (basis_measurable θ i) (basis_continuousOn hθ i)

theorem basis_memLp {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Fin 5) :
    MemLp (basisFunction θ i) 2 (referenceMeasure R) := by
  letI := reference_finite hR
  exact (basis_memLp_top hθ i).mono_exponent le_top

def basisVector {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Fin 5) : Space R := (basis_memLp hR hθ i).toLp _

theorem basisVector_ae {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Fin 5) :
    (basisVector hR hθ i : E→ℝ)=ᵐ[referenceMeasure R] basisFunction θ i :=
  (basis_memLp hR hθ i).coeFn_toLp

def synthesis {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Parameter→L[ℝ]Space R :=
  ∑i : Fin 5,(ContinuousLinearMap.proj i).smulRight (basisVector hR hθ i)

theorem synthesis_apply {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    synthesis hR hθ b=∑i : Fin 5,b i • basisVector hR hθ i := by
  simp only [synthesis,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

theorem finite_sum_ae {X I : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset I) (f : I→Lp ℝ 2 μ) :
    (↑(∑i∈s,f i) : X→ℝ)=ᵐ[μ] (fun x=>∑i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℝ 2 μ)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑j∈s,f j),ih] with x hx hs
    rw [hx]
    change f i x+(∑j∈s,f j) x=f i x+∑j∈s,f j x
    rw [hs]

theorem synthesis_ae {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    (synthesis hR hθ b : E→ℝ)=ᵐ[referenceMeasure R]
      (fun k=>profile θ k*Entropy.denominator euclideanFive b k) := by
  rw [synthesis_apply]
  have ha := ae_all_iff.mpr (fun i=>basisVector_ae hR hθ i)
  have hs := finite_sum_ae Finset.univ (fun i : Fin 5=>b i • basisVector hR hθ i)
  have ht := ae_all_iff.mpr (fun i : Fin 5=>Lp.coeFn_smul (b i) (basisVector hR hθ i))
  filter_upwards [ha,hs,ht] with k hk hsk htk
  rw [hsk]
  simp only [Entropy.denominator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [htk i]
  simp only [Pi.smul_apply,smul_eq_mul,hk i]
  change b i*(profile θ k*euclideanFive i k)=profile θ k*(b i*euclideanFive i k)
  ring

def analysisMap {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Space R→L[ℝ]Parameter :=
  ContinuousLinearMap.pi (fun i=>ReferenceMomentFunctionals.moment hR (basis_memLp_top hθ i))

theorem analysisMap_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) (i : Fin 5) :
    analysisMap hR hθ u i=∫k,u k*basisFunction θ i k∂cubeVolume R :=
  moment_apply hR (basis_memLp_top hθ i) u

theorem basis_coordinate (θ : Parameter) (i : Fin 5) (p : Momentum) :
    basisFunction θ i (toMomentumE p)=Entropy.rj Entropy.fiveInvariants θ p*
      Entropy.fiveInvariants i p := by
  rw [basisFunction,euclideanFive_coordinate]
  rfl

theorem basis_product_integrable {R : ℝ} {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i j : Fin 5) :
    Integrable (fun k=>basisFunction θ i k*basisFunction θ j k) (cubeVolume R) :=
  ((basis_continuousOn hθ i).mul (basis_continuousOn hθ j)).integrableOn_compact
    (FiberContinuity.cube_isCompact R)

theorem basis_gram {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i j : Fin 5) :
    (∫k,basisFunction θ i k*basisFunction θ j k∂cubeVolume R)=gramMatrix R θ i j := by
  calc
    _ = ∫p,basisFunction θ i (toMomentumE p)*basisFunction θ j (toMomentumE p)
      ∂Entropy.cubeMeasure R := thermodynamic_cube_integral R _
        (basis_product_integrable hθ i j).aestronglyMeasurable
    _ = gramMatrix R θ i j := ?_
  apply integral_congr_ae
  filter_upwards [] with p
  rw [basis_coordinate,basis_coordinate]
  ring

end
end Resonance.PhysicalFiveBasis
