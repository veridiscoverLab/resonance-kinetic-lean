import Resonance.PinnedClassificationFinal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The paper's three probability Haar factors are the exact quotient of
the normalized original Euclidean half-open cell, including its seams. -/
open Set MeasureTheory
namespace Resonance.PinnedCellHaar
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedClassificationFinal PinnedCircleAE
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem mk_Ico_preserving : MeasurePreserving (fun x:ℝ=>(x:PinnedPeriodicity.Circle))
    (volume.restrict (Ico 0 period)) circleVolume := by
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa only [zero_add] using AddCircle.measurePreserving_mk period 0

theorem quotient_cell_preserving : MeasurePreserving quotientCoordinates
    (volume.restrict fundamentalCell) (Measure.pi (fun _:Fin 3=>circleVolume)) := by
  let C : Set (Fin 3→ℝ) := univ.pi (fun _=>Ico 0 period)
  have hC : MeasurableSet C := MeasurableSet.univ_pi (fun _=>measurableSet_Ico)
  have h1 : MeasurePreserving (WithLp.ofLp : Ambient→Fin 3→ℝ)
      (volume.restrict fundamentalCell) (volume.restrict C) := by
    have he : WithLp.ofLp ⁻¹' C=fundamentalCell := by
      ext k
      simp [C,fundamentalCell]
    simpa only [he] using (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage hC
  have h2 := measurePreserving_pi (fun _:Fin 3=>volume.restrict (Ico 0 period))
    (fun _:Fin 3=>circleVolume) (fun _=>mk_Ico_preserving)
  have hm : (volume : Measure (Fin 3→ℝ)).restrict C=
      Measure.pi (fun _:Fin 3=>volume.restrict (Ico 0 period)) := by
    exact Measure.restrict_pi_pi (fun _:Fin 3=>volume) (fun _=>Ico 0 period)
  rw [←hm] at h2
  exact h2.comp h1

theorem probability_product_normalization :
    Measure.pi (fun _:Fin 3=>circleHaar)=
      (ENNReal.ofReal period)⁻¹^3 • Measure.pi (fun _:Fin 3=>circleVolume) := by
  apply Measure.pi_eq
  intro S _
  simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_pi,circleHaar]
  rw [Finset.prod_mul_distrib]
  simp

theorem quotient_probability_preserving : MeasurePreserving quotientCoordinates
    ((ENNReal.ofReal period)⁻¹^3 • volume.restrict fundamentalCell)
    (Measure.pi (fun _:Fin 3=>circleHaar)) := by
  rw [probability_product_normalization]
  exact quotient_cell_preserving.smul_measure _

theorem probability_cell_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : CircleMomenta→E) (hf : AEStronglyMeasurable f
      (Measure.pi (fun _:Fin 3=>circleHaar))) :
    (∫k,f k ∂Measure.pi (fun _:Fin 3=>circleHaar))=
      (period^3)⁻¹ • ∫k in fundamentalCell,f (quotientCoordinates k) := by
  rw [←quotient_probability_preserving.map_eq]
  rw [integral_map quotientCoordinates_continuous.measurable.aemeasurable
    (by simpa only [quotient_probability_preserving.map_eq] using hf)]
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofReal period_pos.le,
    inv_pow]

theorem probability_cell_integrable {E : Type*} [NormedAddCommGroup E]
    {f : CircleMomenta→E} (hf : AEStronglyMeasurable f
      (Measure.pi (fun _:Fin 3=>circleHaar)))
    (hi : IntegrableOn (fun k=>f (quotientCoordinates k)) fundamentalCell) :
    Integrable f (Measure.pi (fun _:Fin 3=>circleHaar)) := by
  rw [←quotient_probability_preserving.map_eq]
  apply (integrable_map_measure
    (by simpa only [quotient_probability_preserving.map_eq] using hf)
    quotientCoordinates_continuous.measurable.aemeasurable).mpr
  have h0 : ENNReal.ofReal period≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr period_pos)
  exact hi.smul_measure (by finiteness)

end
end Resonance.PinnedCellHaar
