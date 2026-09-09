import Resonance.EnergyCoordinateFubini

/-! Exact Euclidean volume splitting for the critical coordinates (q,u,v).
The plane variable is (u,v) and the energy-factor variable is q. -/
open Set MeasureTheory
namespace Resonance.CriticalCoordinateFubini
noncomputable section
open LinearSurfaceArea

def split : A ≃ᵐ P × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))).trans MeasurableEquiv.prodComm))

def join (x : P) (q : ℝ) : A := WithLp.toLp 2 ![q,x 0,x 1]

theorem split_volume_preserving : MeasurePreserving split := by
  exact (PiLp.volume_preserving_ofLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.prod (MeasurePreserving.id volume)
        (PiLp.volume_preserving_toLp (Fin 2))).trans Measure.measurePreserving_swap))

theorem split_join (x : P) (q : ℝ) : split (join x q)=(x,q) := by
  ext i
  · fin_cases i <;> rfl
  · rfl

theorem split_symm_apply (p : P × ℝ) : split.symm p=join p.1 p.2 := by
  apply split.injective
  rw [split.apply_symm_apply,split_join]

theorem split_continuous : Continuous (split : A → P × ℝ) := by
  apply Continuous.prodMk
  · apply (PiLp.continuous_toLp 2 (fun _ : Fin 2=>ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> exact PiLp.continuous_apply 2 (fun _ : Fin 3=>ℝ) _
  · exact PiLp.continuous_apply 2 (fun _ : Fin 3=>ℝ) 0

theorem split_symm_continuous : Continuous (split.symm : P × ℝ → A) := by
  rw [show (split.symm : P × ℝ → A)=fun p=>join p.1 p.2 from funext split_symm_apply]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3=>ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [join] <;> fun_prop

theorem split_compact_support {E : Type*} [Zero E] {B : A → E}
    (hB : HasCompactSupport B) : HasCompactSupport (B ∘ split.symm) := by
  apply HasCompactSupport.of_support_subset_isCompact (hB.image split_continuous)
  intro p hp
  exact ⟨split.symm p,subset_tsupport B hp,split.apply_symm_apply p⟩

end
end Resonance.CriticalCoordinateFubini
