import Resonance.ActualGainSmooth
import Resonance.BoundedSourceMaps

/-! Smooth original five-moment analysis and synthesis on fixed spaces.
The moment functionals are the actual unweighted integrals, including
their weighted-domain integrability; no moving projection is assumed smooth. -/
open MeasureTheory Set
open scoped ENNReal ContDiff BigOperators
namespace Resonance.BasisBanachSmooth
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics WeightedJointMeasure ReferenceFrequencySpace
open ActualPairNormalization PhysicalFiveBasis ProfileBanachSmooth LinftyMultiplication

def basisContinuous (R : ℝ) (θ : Parameter) (i : Fin 5) : C(cube R,ℝ) :=
  profileMap R θ*invariantContinuous R i

theorem basisContinuous_contDiffAt {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i : Fin 5) : ContDiffAt ℝ ∞ (fun β=>basisContinuous R β i) θ :=
  (profileMap_contDiffAt hθ).mul contDiffAt_const

theorem basisContinuous_eq {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    basisContinuous R θ i=LinftyFiveAugmentation.continuousBasis hθ i := by
  ext k
  change profileMap R θ k*invariantContinuous R i k=basisFunction θ i k
  rw [profileMap_apply hθ]
  rfl

def basisTop (R : ℝ) (θ : Parameter) (i : Fin 5) : X R :=
  CubeLinftyCoordinates.embed R (basisContinuous R θ i)

theorem basisTop_contDiffAt {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i : Fin 5) : ContDiffAt ℝ ∞ (fun β=>basisTop R β i) θ :=
  (CubeLinftyCoordinates.embed R).contDiff.contDiffAt.comp θ (basisContinuous_contDiffAt hθ i)

theorem basisTop_ae {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    basisTop R θ i=ᵐ[cubeVolume R] basisFunction θ i := by
  filter_upwards [CubeLinftyCoordinates.embed_ae R (basisContinuous R θ i),
    ae_restrict_mem (measurable_cube R)] with k he hk
  change basisTop R θ i k=_ at he
  rw [he,CubeLinftyCoordinates.zeroExtension_apply R _ ⟨k,hk⟩,basisContinuous_eq hθ]
  rfl

def analysisFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : Space R→L[ℝ]Parameter :=
  ∑i : Fin 5,(BoundedSourceMaps.functionalMap hR (basisTop R θ i)).smulRight (Pi.single i 1)

theorem analysisFamily_apply {R : ℝ} (hR : 0<R) (θ : Parameter) (u : Space R) (i : Fin 5) :
    analysisFamily hR θ u i=BoundedSourceMaps.functionalMap hR (basisTop R θ i) u := by
  classical
  simp [analysisFamily,ContinuousLinearMap.smulRight_apply,Pi.single_apply]

theorem analysisFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    analysisFamily hR θ=analysisMap hR hθ := by
  apply ContinuousLinearMap.ext
  intro u
  funext i
  rw [analysisFamily_apply,analysisMap_apply]
  change BoundedSourceMaps.functional hR (basisTop R θ i) u=_
  rw [BoundedSourceMaps.functional_apply]
  apply integral_congr_ae
  filter_upwards [basisTop_ae hθ i] with k hk
  rw [hk]

theorem analysisFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (analysisFamily hR) θ := by
  apply ContDiffAt.sum
  intro i _
  exact ((BoundedSourceMaps.functionalMap hR).contDiff.contDiffAt.comp θ
    (basisTop_contDiffAt hθ i)).smulRight contDiffAt_const

def synthesisContinuousFamily (R : ℝ) (θ : Parameter) : Parameter→L[ℝ]C(cube R,ℝ) :=
  ∑i : Fin 5,(ContinuousLinearMap.proj i).smulRight (basisContinuous R θ i)

theorem synthesisContinuousFamily_contDiffAt {R : ℝ} {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (synthesisContinuousFamily R) θ := by
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.smulRight (basisContinuous_contDiffAt hθ i)

def synthesisFamily (R : ℝ) (θ : Parameter) : Parameter→L[ℝ]X R :=
  (CubeLinftyCoordinates.embed R).comp (synthesisContinuousFamily R θ)

theorem synthesisFamily_eq {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    synthesisFamily R θ=LinftyFiveAugmentation.synthesisTop hθ := by
  unfold synthesisFamily LinftyFiveAugmentation.synthesisTop
  congr 1
  unfold synthesisContinuousFamily LinftyFiveAugmentation.synthesisContinuous
  apply Finset.sum_congr rfl
  intro i _
  rw [basisContinuous_eq hθ]

theorem synthesisFamily_contDiffAt {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ContDiffAt ℝ ∞ (synthesisFamily R) θ :=
  contDiffAt_const.clm_comp (synthesisContinuousFamily_contDiffAt hθ)

theorem actual_analysisFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (analysisFamily hR) (positiveDomain R) :=
  fun _ hθ=>(analysisFamily_contDiffAt hR hθ).contDiffWithinAt

theorem actual_synthesisFamily_contDiffOn (R : ℝ) :
    ContDiffOn ℝ ∞ (synthesisFamily R) (positiveDomain R) :=
  fun _ hθ=>(synthesisFamily_contDiffAt hθ).contDiffWithinAt

end
end Resonance.BasisBanachSmooth
