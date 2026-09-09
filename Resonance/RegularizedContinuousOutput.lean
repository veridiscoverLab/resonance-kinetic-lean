import Resonance.BoundedResolventUniqueness

/-! Recovery of actual continuous representatives for continuous source
data and a strictly positive shift. This does not assign corner values to
arbitrary L-infinity forcing. -/
open MeasureTheory Set
open scoped ENNReal Topology
namespace Resonance.RegularizedContinuousOutput
noncomputable section
set_option maxHeartbeats 1600000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace PhysicalFiveBasis
open LinftyFiveAugmentation PositiveLossShift ShiftedAugmentation
open ShiftedParameterContinuity ShiftedStrongCell RegularizedCellBounds
open StrongCellParameterContinuity (profileContinuous)

theorem loss_extension_eq {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    {k : E} (hk : k∈cube R) :
    lossFrequency R (profile θ) k=
      lossFrequency R (FiberContinuity.continuousExtension R (profileContinuous hθ)) k := by
  let N := FiberContinuity.continuousExtension R (profileContinuous hθ)
  have he (p : E) (hp : p∈cube R) : N p=profile θ p :=
    FiberContinuity.continuousExtension_eq R (profileContinuous hθ) ⟨p,hp⟩
  change lossFrequency R (profile θ) k=lossFrequency R N k
  unfold lossFrequency FiberContinuity.fiberReadout
  rw [he k hk]
  congr 1
  apply integral_congr_ae
  filter_upwards [CollisionFiber.fiber_support R k] with q hq
  rw [he (q 1) (hq.1 1),he (q 2) (hq.1 2),he (q 3) (hq.1 3)]

theorem actual_loss_continuousOn {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContinuousOn (lossFrequency R (profile θ)) (cube R) := by
  have hp (k : E) (hk : k∈cube R) :
      0<FiberContinuity.continuousExtension R (profileContinuous hθ) k := by
    rw [FiberContinuity.continuousExtension_eq R (profileContinuous hθ) ⟨k,hk⟩]
    exact profile_pos hθ hk
  exact (lossFrequency_continuousOn hR.le
    (FiberContinuity.continuousExtension R (profileContinuous hθ)).continuous hp).congr
      (fun k hk=>loss_extension_eq hθ hk)

def lossContinuous {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : C(cube R,ℝ) :=
  ⟨fun k=>lossFrequency R (profile θ) k,(actual_loss_continuousOn hR hθ).restrict⟩

def continuousCoordinate {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : C(cube R,ℝ)) : C(cube R,ℝ) :=
  F-AmbientLinftyCompact.continuousOutput hR hθ
    (multiplier hR hθ hz (shiftedCoordinate hR hθ hz (CubeLinftyCoordinates.embed R F)))-
      synthesisContinuous hθ (analysisMap hR hθ
        (shiftedCell hR hθ hz (CubeLinftyCoordinates.embed R F)))

theorem continuousCoordinate_embed {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : C(cube R,ℝ)) :
    CubeLinftyCoordinates.embed R (continuousCoordinate hR hθ hz F)=
      shiftedCoordinate hR hθ hz (CubeLinftyCoordinates.embed R F) := by
  have he := shifted_augmented_coordinate hR hθ hz (CubeLinftyCoordinates.embed R F)
  unfold continuousCoordinate
  rw [map_sub,map_sub]
  change CubeLinftyCoordinates.embed R F-
      AmbientLinftyCompact.operator hR hθ (multiplier hR hθ hz
        (shiftedCoordinate hR hθ hz (CubeLinftyCoordinates.embed R F)))-
      correction hR hθ (multiplier hR hθ hz
        (shiftedCoordinate hR hθ hz (CubeLinftyCoordinates.embed R F)))=_
  change shiftedCoordinate hR hθ hz (CubeLinftyCoordinates.embed R F)+
    (AmbientLinftyCompact.operator hR hθ (multiplier hR hθ hz
      (shiftedCoordinate hR hθ hz (CubeLinftyCoordinates.embed R F)))+
    correction hR hθ (multiplier hR hθ hz
      (shiftedCoordinate hR hθ hz (CubeLinftyCoordinates.embed R F))))=
        CubeLinftyCoordinates.embed R F at he
  exact (sub_sub _ _ _).trans (eq_sub_iff_add_eq.mpr he).symm

def gapFactor {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0<z) : C(cube R,ℝ) :=
  ⟨fun k=>z/(lossFrequency R (profile θ) k+z),
    continuous_const.div ((lossContinuous hR hθ).continuous.add continuous_const)
      (fun k=>(add_pos_of_nonneg_of_pos (ActualFrequencyRatio.loss_nonnegative hR hθ k.property) hz).ne')⟩

def continuousOutput {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0<z) (F : C(cube R,ℝ)) : C(cube R,ℝ) :=
  gapFactor hR hθ hz*continuousCoordinate hR hθ hz.le F

theorem continuousOutput_embed {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0<z) (F : C(cube R,ℝ)) :
    CubeLinftyCoordinates.embed R (continuousOutput hR hθ hz F)=
      boundedOutput hR hθ hz.le (CubeLinftyCoordinates.embed R F) := by
  have hc := CubeLinftyCoordinates.embed_ae R (continuousCoordinate hR hθ hz.le F)
  rw [continuousCoordinate_embed] at hc
  apply Lp.ext
  filter_upwards [CubeLinftyCoordinates.embed_ae R (continuousOutput hR hθ hz F),hc,
    boundedOutput_ae hR hθ hz.le (CubeLinftyCoordinates.embed R F),
    shiftedDivide_ae hR hθ hz.le (shiftedCoordinate hR hθ hz.le (CubeLinftyCoordinates.embed R F)),
    ae_restrict_mem (measurable_cube R)] with k ho hc hb hu hk
  change shiftedCell hR hθ hz.le (CubeLinftyCoordinates.embed R F) k=
    shiftedCoordinate hR hθ hz.le (CubeLinftyCoordinates.embed R F) k/
      (lossFrequency R (profile θ) k+z) at hu
  rw [ho,hb,hu,hc,CubeLinftyCoordinates.zeroExtension_apply R _ ⟨k,hk⟩,
    CubeLinftyCoordinates.zeroExtension_apply R _ ⟨k,hk⟩]
  change (z/(lossFrequency R (profile θ) k+z))*continuousCoordinate hR hθ hz.le F ⟨k,hk⟩=_
  ring

theorem continuousOutput_is_actual_physical_vector {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0<z) (F : C(cube R,ℝ)) :
    CubeLinftyCoordinates.zeroExtension R (continuousOutput hR hθ hz F)=ᵐ[cubeVolume R]
      (z • shiftedCell hR hθ hz.le (CubeLinftyCoordinates.embed R F) : Space R) := by
  have he := CubeLinftyCoordinates.embed_ae R (continuousOutput hR hθ hz F)
  rw [continuousOutput_embed] at he
  have hzv := (reference_volume_equivalent hR).1.ae_eq
    (Lp.coeFn_smul z (shiftedCell hR hθ hz.le (CubeLinftyCoordinates.embed R F)))
  exact he.symm.trans ((boundedOutput_ae hR hθ hz.le (CubeLinftyCoordinates.embed R F)).trans hzv.symm)

end
end Resonance.RegularizedContinuousOutput
