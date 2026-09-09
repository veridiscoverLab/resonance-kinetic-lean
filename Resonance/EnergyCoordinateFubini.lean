import Resonance.CoordinateLevelGraph
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The actual Euclidean three-volume splits into the middle energy coordinate
and the remaining Euclidean plane. All integral identities use this concrete
volume-preserving equivalence, not an assumed disintegration. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.EnergyCoordinateFubini
noncomputable section
open LinearSurfaceArea CoordinateLevelGraph

def split : A ≃ᵐ ℝ × P :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem split_volume_preserving : MeasurePreserving split := by
  exact (PiLp.volume_preserving_ofLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans
      (MeasurePreserving.prod (MeasurePreserving.id volume)
        (PiLp.volume_preserving_toLp (Fin 2))))

theorem split_levelEmbedding (s : ℝ) (x : P) : split (levelEmbedding s x)=(s,x) := by
  ext i
  · rfl
  · fin_cases i <;> rfl

theorem split_symm_apply (p : ℝ × P) : split.symm p=levelEmbedding p.1 p.2 := by
  apply split.injective
  rw [split.apply_symm_apply,split_levelEmbedding]

theorem split_continuous : Continuous (split : A → ℝ × P) := by
  apply Continuous.prodMk
  · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  · apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) _

theorem split_symm_continuous : Continuous (split.symm : ℝ × P → A) := by
  have he : (split.symm : ℝ × P → A)=fun p=>levelEmbedding p.1 p.2 :=
    funext split_symm_apply
  rw [he]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [levelEmbedding] <;> fun_prop

theorem split_compact_support {E : Type*} [Zero E] {B : A → E}
    (hB : HasCompactSupport B) : HasCompactSupport (B ∘ split.symm) := by
  apply HasCompactSupport.of_support_subset_isCompact (hB.image split_continuous)
  intro p hp
  exact ⟨split.symm p,subset_tsupport B hp,split.apply_symm_apply p⟩

theorem lintegral_energy_plane (B : A → ℝ≥0∞) (hB : Measurable B) :
    ∫⁻q,B q=∫⁻s,∫⁻x,B (levelEmbedding s x) := by
  rw [← split_volume_preserving.symm.lintegral_comp hB]
  change ∫⁻q:ℝ × P,(B ∘ split.symm) q ∂volume.prod volume=_
  rw [lintegral_prod _ (hB.comp split.symm.measurable).aemeasurable]
  simp only [Function.comp_apply,split_symm_apply]

theorem integral_energy_plane {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (B : A → E) (hB : Integrable B) :
    ∫q,B q=∫s,∫x,B (levelEmbedding s x) := by
  have hi : Integrable (B ∘ split.symm) :=
    split_volume_preserving.symm.integrable_comp hB.aestronglyMeasurable |>.mpr hB
  rw [← split_volume_preserving.symm.integral_comp split.symm.measurableEmbedding B]
  change ∫q:ℝ × P,(B ∘ split.symm) q ∂volume.prod volume=_
  rw [integral_prod _ hi]
  simp only [Function.comp_apply,split_symm_apply]

end
end Resonance.EnergyCoordinateFubini
