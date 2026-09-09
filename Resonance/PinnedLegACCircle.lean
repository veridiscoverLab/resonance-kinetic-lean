import Resonance.PinnedLegAC
import Resonance.PinnedClassificationFinal

/-! The full four-leg absolute-continuity statement in the paper's periodic
and Euclidean-area normalizations.  No restriction to selected charts occurs. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Resonance.PinnedLegACCircle
noncomputable section
open Resonance.PinnedMeasure Resonance.PinnedPeriodicity Resonance.PinnedCircleAE
open Resonance.PinnedLegAC Resonance.PinnedMeasureNormalization
open Resonance.PinnedClassificationFinal
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

def circleLeg (i : Fin 4) (k : CircleMomenta) : PinnedPeriodicity.Circle :=
  ![k 0,k 1,k 2,k 0+k 1-k 2] i

theorem circleLeg_continuous (i : Fin 4) : Continuous (circleLeg i) := by
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2
  · change Continuous (fun k : CircleMomenta => k 0+k 1-k 2)
    fun_prop

theorem circleLeg_quotient (i : Fin 4) (k : Ambient) :
    circleLeg i (quotientCoordinates k)=(realLeg i k:PinnedPeriodicity.Circle) := by
  fin_cases i <;> simp [circleLeg,quotientCoordinates,realLeg,PinnedGeometry.liftLegs]

theorem circle_quotient_preimage_null {E : Set PinnedPeriodicity.Circle}
    (hE : MeasurableSet E) (hnull : circleVolume E=0) :
    volume ((fun x : ℝ => (x:PinnedPeriodicity.Circle)) ⁻¹' E)=0 := by
  let S := (fun x : ℝ => (x:PinnedPeriodicity.Circle)) ⁻¹' E
  change volume S=0
  apply measure_null_of_locally_null S
  intro x _
  let t := x-period/2
  let I := Ioc t (t+period)
  have mp := AddCircle.measurePreserving_mk period t
  have hzero : (volume.restrict I) S=0 := by
    rw [← Measure.map_apply mp.measurable hE,mp.map_eq]
    exact hnull
  have hz : volume (S∩I)=0 := by
    rw [Measure.restrict_apply' measurableSet_Ioc] at hzero
    exact hzero
  have hI : I ∈ 𝓝 x := by
    apply Ioc_mem_nhds <;> dsimp [t] <;> linarith [period_pos]
  exact ⟨S∩I,inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hI),hz⟩

theorem circle_quotient_absolutelyContinuous :
    (volume : Measure ℝ).map (fun x : ℝ => (x:PinnedPeriodicity.Circle)) ≪ circleVolume := by
  have hm : Measurable (fun x : ℝ => (x:PinnedPeriodicity.Circle)) :=
    (AddCircle.continuous_mk' period).measurable
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hnull
  rw [Measure.map_apply hm hE]
  exact circle_quotient_preimage_null hE hnull

theorem circle_coarea_leg_absolutelyContinuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (i : Fin 4) : (circleRegularCoarea d).map (circleLeg i) ≪ circleVolume := by
  have hm : Measurable (fun x : ℝ => (x:PinnedPeriodicity.Circle)) :=
    (AddCircle.continuous_mk' period).measurable
  have hcell : cellCoarea d ≪ liftedRegularCoarea d :=
    Measure.restrict_le_self.absolutelyContinuous
  have hreal : (cellCoarea d).map (realLeg i) ≪ volume :=
    (hcell.map (realLeg_continuous i).measurable).trans
      (lifted_coarea_leg_absolutelyContinuous hd0 hdU i)
  have hcircle := (hreal.map hm).trans
    circle_quotient_absolutelyContinuous
  have heq : (circleRegularCoarea d).map (circleLeg i)=
      ((cellCoarea d).map (realLeg i)).map (fun x : ℝ => (x:PinnedPeriodicity.Circle)) := by
    unfold circleRegularCoarea
    rw [Measure.map_map (circleLeg_continuous i).measurable quotientCoordinates_continuous.measurable,
      Measure.map_map hm (realLeg_continuous i).measurable]
    congr 1
    funext k
    exact circleLeg_quotient i k
  rw [heq]
  exact hcircle

/-- The exact paper statement: all four marginals of the original regular
Euclidean coarea on the periodic resonance surface are dominated by probability
Haar measure.  All fixed parameters 0<d<1/2 are covered. -/
theorem full_coarea_all_legs_absolutelyContinuous {d : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (i : Fin 4) :
    (euclideanCircleRegularCoarea d).map (circleLeg i) ≪ circleHaar := by
  exact (((circle_coarea_mutually_absolutelyContinuous d).1.map
    (circleLeg_continuous i).measurable).trans
      (circle_coarea_leg_absolutelyContinuous hd0 hdU i)).trans
        circleHaar_mutually_absolutelyContinuous.2

theorem full_coarea_ae_comp {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (i : Fin 4) {p : PinnedPeriodicity.Circle → Prop}
    (hp : ∀ᵐ k ∂circleHaar, p k) :
    ∀ᵐ k ∂euclideanCircleRegularCoarea d, p (circleLeg i k) :=
  ae_of_ae_map (circleLeg_continuous i).measurable.aemeasurable
    ((full_coarea_all_legs_absolutelyContinuous hd0 hdU i).ae_le hp)

/-- Changing representatives on a Haar-null set preserves the complete
four-leg invariant relation on the entire original regular coarea.  Neither
representative is required to be Borel measurable in this transfer lemma. -/
theorem full_coarea_invariant_ae_congr {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ ψ : PinnedPeriodicity.Circle → ℂ} (he : φ =ᵐ[circleHaar] ψ) :
    (fun k => circleInvariantRelation φ k) =ᵐ[euclideanCircleRegularCoarea d]
      (fun k => circleInvariantRelation ψ k) := by
  filter_upwards [full_coarea_ae_comp hd0 hdU 0 he,
    full_coarea_ae_comp hd0 hdU 1 he,full_coarea_ae_comp hd0 hdU 2 he,
    full_coarea_ae_comp hd0 hdU 3 he] with k h0 h1 h2 h3
  change (φ (circleLeg 0 k)+φ (circleLeg 1 k)=φ (circleLeg 2 k)+φ (circleLeg 3 k)) =
    (ψ (circleLeg 0 k)+ψ (circleLeg 1 k)=ψ (circleLeg 2 k)+ψ (circleLeg 3 k))
  rw [h0,h1,h2,h3]

theorem full_coarea_invariant_iff_of_ae_eq {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ ψ : PinnedPeriodicity.Circle → ℂ} (he : φ =ᵐ[circleHaar] ψ) :
    euclideanCircleInvariant d φ ↔ euclideanCircleInvariant d ψ := by
  exact Filter.eventually_congr ((full_coarea_invariant_ae_congr hd0 hdU he).mono
    (fun _ h => Iff.of_eq h))

end
end Resonance.PinnedLegACCircle
