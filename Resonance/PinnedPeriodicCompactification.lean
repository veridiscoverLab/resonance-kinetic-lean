import Resonance.PeriodicHatCells
import Resonance.FinitePeriodicIntegral
import Resonance.PinnedMeasureNormalization

/-! Exact return from one continuous compact source to the original half-open
period cell. Both the Euclidean volume and the original Euclidean coarea use
the same eight actual lattice shifts and the same partition. -/
open Set MeasureTheory
namespace Resonance.PinnedPeriodicCompactification
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCompactLocalization
open PinnedMeasureNormalization PeriodicHatPartition PeriodicHatCells

theorem euclidean_coarea_translation_preserving {d : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (n : Fin 3 → ℤ) :
    MeasurePreserving (translation n) (euclideanLiftedRegularCoarea d)
      (euclideanLiftedRegularCoarea d) := by
  rw [euclideanLiftedRegularCoarea_eq_smul]
  exact (coarea_translation_preserving hd0 hdU n).smul_measure _

theorem compactification {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ambient)
    (hMP : ∀n:Fin 3→ℤ,MeasurePreserving (translation n) μ μ)
    (f : Ambient → E) (hp : ∀n k,f (translation n k)=f k)
    (hi : Integrable (fun k=>weight k • f k) μ) :
    IntegrableOn f fundamentalCell μ ∧
      (∫k,weight k • f k ∂μ)=∫k in fundamentalCell,f k ∂μ := by
  exact FinitePeriodicIntegral.compactification μ
    (fun i:Index=>(translation (winding i)).toHomeomorph.toMeasurableEquiv)
    (fun i=>hMP (winding i)) fundamentalCell_measurable
    translatedCells_pairwise_disjoint weight f
    (fun _ hk=>weight_support_covered hk) (fun _ hx=>weight_finite_partition hx)
    (fun i k _=>hp (winding i) k) hi

theorem volume_compactification {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Ambient → E) (hp : ∀n k,f (translation n k)=f k)
    (hi : Integrable (fun k=>weight k • f k)) :
    IntegrableOn f fundamentalCell ∧
      (∫k,weight k • f k)=∫k in fundamentalCell,f k := by
  exact compactification volume
    (fun n=>measurePreserving_add_right volume (latticeShift n)) f hp hi

theorem coarea_compactification {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (f : Ambient → E) (hp : ∀n k,f (translation n k)=f k)
    (hi : Integrable (fun k=>weight k • f k) (euclideanLiftedRegularCoarea d)) :
    Integrable f (euclideanCellCoarea d) ∧
      (∫k,weight k • f k ∂euclideanLiftedRegularCoarea d)=
        ∫k,f k ∂euclideanCellCoarea d := by
  exact compactification _ (euclidean_coarea_translation_preserving hd0 hdU) f hp hi

end
end Resonance.PinnedPeriodicCompactification
