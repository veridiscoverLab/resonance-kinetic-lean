import Resonance.PinnedCriticalVolume
import Resonance.CoordinatePermutation

/-! Genuine homeomorphisms for the original critical gauges. Their volume
preservation is exact; no Euclidean surface invariance under shear is asserted. -/
open Set MeasureTheory
namespace Resonance.PinnedCriticalGauge
noncomputable section
open PinnedMeasure PinnedCriticalNormalization PinnedCriticalVolume
open PinnedCriticalCancellation PinnedPeriodicity CoordinatePermutation

def rectangleHomeomorph : Ambient ≃ₜ Ambient where
  toFun := rectangleMap
  invFun := rectangleInverse
  left_inv := rectangleInverse_map
  right_inv := rectangleMap_inverse
  continuous_toFun := rectangleMap.continuous
  continuous_invFun := rectangleInverse.continuous

def gaugeHomeomorph (swap : Bool) (n m : ℤ) : Ambient ≃ₜ Ambient :=
  (rectangleHomeomorph.trans (Homeomorph.addRight (latticeShift ![n,m,0]))).trans
    (if swap then (swapMiddle 0).toHomeomorph else Homeomorph.refl Ambient)

theorem gaugeHomeomorph_apply (swap : Bool) (n m : ℤ) (p : Ambient) :
    gaugeHomeomorph swap n m p=criticalGauge swap n m p := by
  cases swap
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem gauge_volume_preserving (swap : Bool) (n m : ℤ) :
    MeasurePreserving (gaugeHomeomorph swap n m) volume volume := by
  have he : (gaugeHomeomorph swap n m : Ambient → Ambient)=criticalGauge swap n m :=
    funext (gaugeHomeomorph_apply swap n m)
  rw [he]
  exact criticalGauge_volume_preserving swap n m

theorem gauge_energy (d : ℝ) (swap : Bool) (n m : ℤ) (p : Ambient) :
    liftedEnergy d (gaugeHomeomorph swap n m p)=PinnedLocalArea.rectangleEnergy d p := by
  rw [gaugeHomeomorph_apply,criticalGauge_energy]

theorem gauge_difference {φ : ℝ → ℂ} (hp : Function.Periodic φ period)
    (swap : Bool) (n m : ℤ) (p : Ambient) :
    fullDifference φ (gaugeHomeomorph swap n m p)=fullDifference φ (rectangleMap p) := by
  rw [gaugeHomeomorph_apply,fullDifference_gauge hp]

theorem gauge_compact_support {E : Type*} [Zero E] {B : Ambient → E}
    (hB : HasCompactSupport B) (swap : Bool) (n m : ℤ) :
    HasCompactSupport (B ∘ gaugeHomeomorph swap n m) := by
  let e := gaugeHomeomorph swap n m
  apply HasCompactSupport.of_support_subset_isCompact (hB.image e.symm.continuous)
  intro p hp
  exact ⟨e p,subset_tsupport B hp,e.symm_apply_apply p⟩

theorem gauge_integrable_iff {E : Type*} [NormedAddCommGroup E]
    {B : Ambient → E} (swap : Bool) (n m : ℤ) :
    Integrable (B ∘ gaugeHomeomorph swap n m) ↔ Integrable B :=
  (gauge_volume_preserving swap n m).integrable_comp_emb
    (gaugeHomeomorph swap n m).toMeasurableEquiv.measurableEmbedding

theorem gauge_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Ambient → E) (swap : Bool) (n m : ℤ) :
    ∫p,B (gaugeHomeomorph swap n m p)=∫k,B k :=
  (gauge_volume_preserving swap n m).integral_comp
    (gaugeHomeomorph swap n m).toMeasurableEquiv.measurableEmbedding B

end
end Resonance.PinnedCriticalGauge
