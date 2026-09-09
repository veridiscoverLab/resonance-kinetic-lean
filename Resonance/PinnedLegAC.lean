import Resonance.PinnedCriticalCurves
import Resonance.PinnedVelocityLevels
import Resonance.PinnedCircleAE

/-! Absolute continuity of every leg of the complete regular coarea measure.
The proof retains all real lifts, including trivial branches and Umklapp shifts. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedLegAC
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedCharts Resonance.PinnedMeasure
open Resonance.PinnedSurfaceNull Resonance.PinnedCriticalCurves
open Resonance.PinnedVelocityLevels Resonance.PinnedPeriodicity Resonance.PinnedCircleAE

theorem velocity_contDiff_one {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    ContDiff ℝ 1 (velocity d) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  unfold velocity
  exact (contDiff_const.mul contDiff_sin).div (signed_omega_contDiff hdL hdU 1)
    (fun x => (signed_omega_pos hdL hdU x).ne')

theorem pinned_common_velocity_null {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    (μH[2] : Measure Ambient) (commonVelocitySet (velocity d))=0 :=
  common_velocity_hausdorff_null (velocity_contDiff_one hd0 hdU)
    (velocity_level_countable hd0 hdU) (velocity_critical_countable hd0 hdU)

def exchangeOutgoing : Ambient →L[ℝ] Ambient :=
  ({toFun := fun k => WithLp.toLp 2 ![k 0,k 1,k 0+k 1-k 2]
    map_add' := by intros; ext i; fin_cases i <;> simp; ring
    map_smul' := by intros; ext i; fin_cases i <;> simp; ring
  } : Ambient →ₗ[ℝ] Ambient).toContinuousLinearMap

def exchangeIncoming : Ambient →L[ℝ] Ambient :=
  ({toFun := fun k => WithLp.toLp 2 ![k 1,k 0,k 2]
    map_add' := by intros; ext i; fin_cases i <;> simp
    map_smul' := by intros; ext i; fin_cases i <;> simp
  } : Ambient →ₗ[ℝ] Ambient).toContinuousLinearMap

def exchangePairs : Ambient →L[ℝ] Ambient :=
  ({toFun := fun k => WithLp.toLp 2 ![k 2,k 0+k 1-k 2,k 0]
    map_add' := by intros; ext i; fin_cases i <;> simp; ring
    map_smul' := by intros; ext i; fin_cases i <;> simp; ring
  } : Ambient →ₗ[ℝ] Ambient).toContinuousLinearMap

theorem exchangeOutgoing_involutive (k : Ambient) : exchangeOutgoing (exchangeOutgoing k)=k := by
  ext i
  fin_cases i <;> simp [exchangeOutgoing]

theorem exchangeIncoming_involutive (k : Ambient) : exchangeIncoming (exchangeIncoming k)=k := by
  ext i
  fin_cases i <;> simp [exchangeIncoming]

theorem exchangePairs_involutive (k : Ambient) : exchangePairs (exchangePairs k)=k := by
  ext i
  fin_cases i <;> simp [exchangePairs]

theorem energy_exchangeOutgoing (d : ℝ) (k : Ambient) :
    liftedEnergy d (exchangeOutgoing k)=liftedEnergy d k := by
  change omega d (k 0)+omega d (k 1)-omega d (k 0+k 1-k 2)-
    omega d (k 0+k 1-(k 0+k 1-k 2)) =
    omega d (k 0)+omega d (k 1)-omega d (k 2)-omega d (k 0+k 1-k 2)
  have he : k 0+k 1-(k 0+k 1-k 2)=k 2 := by ring
  rw [he]
  ring

theorem energy_exchangeIncoming (d : ℝ) (k : Ambient) :
    liftedEnergy d (exchangeIncoming k)=liftedEnergy d k := by
  simp [liftedEnergy,energyDefect,exchangeIncoming,add_comm]

theorem energy_exchangePairs (d : ℝ) (k : Ambient) :
    liftedEnergy d (exchangePairs k)= -liftedEnergy d k := by
  change omega d (k 2)+omega d (k 0+k 1-k 2)-omega d (k 0)-
    omega d (k 2+(k 0+k 1-k 2)-k 0) =
    -(omega d (k 0)+omega d (k 1)-omega d (k 2)-omega d (k 0+k 1-k 2))
  have he : k 2+(k 0+k 1-k 2)-k 0=k 1 := by ring
  rw [he]
  ring

theorem linear_image_null (L : Ambient→L[ℝ]Ambient) {S : Set Ambient}
    (hS : (μH[2] : Measure Ambient) S=0) :
    (μH[2] : Measure Ambient) (L '' S)=0 := by
  have hb := L.lipschitz.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2) S
  rw [hS,mul_zero] at hb
  exact le_antisymm hb (zero_le _)

/-- Even before restricting to regular points, a null x-set cuts an H²-null
part out of the whole energy zero set. -/
theorem energy_first_leg_null {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {E : Set ℝ} (hE : MeasurableSet E) (hnull : volume E=0) :
    (μH[2] : Measure Ambient) {k | liftedEnergy d k=0 ∧ k 0∈E}=0 := by
  let G : Set Ambient := {k | liftedEnergy d k=0 ∧ k 0∈E ∧
    velocity d (k 1)≠velocity d (k 0+k 1-k 2)}
  have hG : (μH[2] : Measure Ambient) G=0 := good_first_projection_null hd0 hdU hE hnull
  have hU : (μH[2] : Measure Ambient)
      (G ∪ exchangeOutgoing '' G ∪ commonVelocitySet (velocity d))=0 :=
    measure_union_null (measure_union_null hG (linear_image_null exchangeOutgoing hG))
      (pinned_common_velocity_null hd0 hdU)
  apply measure_mono_null _ hU
  rintro k ⟨he,hkE⟩
  by_cases hyw : velocity d (k 1)=velocity d (k 0+k 1-k 2)
  · by_cases hyz : velocity d (k 1)=velocity d (k 2)
    · exact Or.inr ⟨hyz,hyw⟩
    · apply Or.inl ∘ Or.inr
      refine ⟨exchangeOutgoing k,?_,exchangeOutgoing_involutive k⟩
      refine ⟨by rw [energy_exchangeOutgoing,he],hkE,?_⟩
      simpa [exchangeOutgoing] using hyz
  · exact Or.inl (Or.inl ⟨he,hkE,hyw⟩)

def realLeg (i : Fin 4) (k : Ambient) : ℝ := liftLegs (k 0) (k 1) (k 2) i

theorem realLeg_continuous (i : Fin 4) : Continuous (realLeg i) := by
  fin_cases i
  · exact (coordinateProjection 0).continuous
  · exact (coordinateProjection 1).continuous
  · exact (coordinateProjection 2).continuous
  · exact (coordinateProjection 0+coordinateProjection 1-coordinateProjection 2).continuous

theorem energy_all_legs_null {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (i : Fin 4) {E : Set ℝ} (hE : MeasurableSet E) (hnull : volume E=0) :
    (μH[2] : Measure Ambient) {k | liftedEnergy d k=0 ∧ realLeg i k∈E}=0 := by
  have h0 := energy_first_leg_null hd0 hdU hE hnull
  have h2 : (μH[2] : Measure Ambient) {k | liftedEnergy d k=0 ∧ k 2∈E}=0 := by
    apply measure_mono_null _ (linear_image_null exchangePairs h0)
    rintro k ⟨he,hk⟩
    refine ⟨exchangePairs k,⟨?_,hk⟩,exchangePairs_involutive k⟩
    rw [energy_exchangePairs,he,neg_zero]
  fin_cases i
  · exact h0
  · apply measure_mono_null _ (linear_image_null exchangeIncoming h0)
    rintro k ⟨he,hk⟩
    refine ⟨exchangeIncoming k,⟨?_,hk⟩,exchangeIncoming_involutive k⟩
    rw [energy_exchangeIncoming,he]
  · exact h2
  · apply measure_mono_null _ (linear_image_null exchangeOutgoing h2)
    rintro k ⟨he,hk⟩
    refine ⟨exchangeOutgoing k,⟨?_,hk⟩,exchangeOutgoing_involutive k⟩
    rw [energy_exchangeOutgoing,he]

theorem lifted_coarea_leg_null {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (i : Fin 4) {E : Set ℝ} (hE : MeasurableSet E) (hnull : volume E=0) :
    liftedRegularCoarea d (realLeg i ⁻¹' E)=0 := by
  apply withDensity_absolutelyContinuous _ _
  rw [Measure.restrict_apply' (regularSurface_measurable hd0 hdU)]
  apply measure_mono_null _ (energy_all_legs_null hd0 hdU i hE hnull)
  rintro k ⟨hk,hreg⟩
  exact ⟨hreg.1,hk⟩

/-- All four marginals of the actual full lifted regular coarea are absolutely
continuous.  No marginal boundedness or finite total coarea mass is asserted. -/
theorem lifted_coarea_leg_absolutelyContinuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (i : Fin 4) : (liftedRegularCoarea d).map (realLeg i) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hnull
  rw [Measure.map_apply (realLeg_continuous i).measurable hE]
  exact lifted_coarea_leg_null hd0 hdU i hE hnull

end
end Resonance.PinnedLegAC
