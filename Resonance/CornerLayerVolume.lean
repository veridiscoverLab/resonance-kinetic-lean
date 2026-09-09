import Resonance.CornerFrequencyBounds
import Resonance.CoareaNormalization

/-! Actual Euclidean-volume bounds for the eight corner layers of the same
sharp cube used by the full collision measure. The dimensionless depth is
the frozen CornerFrequencyBounds.cornerDepth; no volume law is assumed. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.CornerLayerVolume
noncomputable section
open ResonantMeasure CornerFrequencyBounds CubeFrequencyReflection
open CoareaNormalization (toMomentumE toMomentumE_map_volume toMomentumE_volume_preserving)
set_option maxHeartbeats 600000

def edgeIntervals (R ρ : ℝ) : Set ℝ := Icc (-R) (-R+ρ) ∪ Icc (R-ρ) R

theorem edgeIntervals_volume_le (R ρ : ℝ) :
    volume (edgeIntervals R ρ) ≤ 2 * ENNReal.ofReal ρ := by
  apply (measure_union_le _ _).trans_eq
  rw [Real.volume_Icc,Real.volume_Icc]
  have h₁ : -R+ρ-(-R)=ρ := by ring
  have h₂ : R-(R-ρ)=ρ := by ring
  rw [h₁,h₂,two_mul]

theorem coordinate_mem_edgeIntervals {R ρ x : ℝ}
    (hx : |x| ≤ R) (hl : R-ρ ≤ |x|) : x ∈ edgeIntervals R ρ := by
  rcases le_total 0 x with h|h
  · apply Or.inr
    rw [abs_of_nonneg h] at hx hl
    exact ⟨hl,hx⟩
  · apply Or.inl
    rw [abs_of_nonpos h] at hx hl
    constructor <;> linarith

def coordinateLayer (R ρ : ℝ) : Set E :=
  {k | ∀ i : Fin 3, |k i| ≤ R ∧ R-ρ ≤ |k i|}

theorem coordinateLayer_measurable (R ρ : ℝ) : MeasurableSet (coordinateLayer R ρ) := by
  change MeasurableSet {k : E | ∀ i : Fin 3, |k i| ≤ R ∧ R-ρ ≤ |k i|}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have ha : Continuous (fun k : E => |k i|) := by fun_prop
  exact (isClosed_le ha continuous_const).measurableSet.inter
    (isClosed_le continuous_const ha).measurableSet

theorem coordinateLayer_preimage_subset (R ρ : ℝ) :
    toMomentumE ⁻¹' coordinateLayer R ρ ⊆
      Set.pi Set.univ (fun _ : Fin 3 => edgeIntervals R ρ) := by
  intro k hk i _
  exact coordinate_mem_edgeIntervals (hk i).1 (hk i).2

theorem coordinateLayer_volume_le (R ρ : ℝ) :
    volume (coordinateLayer R ρ) ≤ 8 * (ENNReal.ofReal ρ)^3 := by
  rw [← toMomentumE_map_volume,Measure.map_apply toMomentumE_volume_preserving.measurable
    (coordinateLayer_measurable R ρ)]
  apply (measure_mono (coordinateLayer_preimage_subset R ρ)).trans
  rw [volume_pi_pi]
  calc
    ∏ _ : Fin 3, volume (edgeIntervals R ρ) ≤ ∏ _ : Fin 3, 2*ENNReal.ofReal ρ :=
      Finset.prod_le_prod' (fun _ _ => edgeIntervals_volume_le R ρ)
    _ = 8*(ENNReal.ofReal ρ)^3 := by simp [mul_pow]; norm_num

/-- Physical (unscaled) largest distance to a nearest coordinate face. -/
def physicalDepth (R : ℝ) (k : E) : ℝ :=
  max (R-|k 0|) (max (R-|k 1|) (R-|k 2|))

theorem physicalDepth_le_iff (R ρ : ℝ) (k : E) :
    physicalDepth R k ≤ ρ ↔ ∀ i : Fin 3, R-|k i| ≤ ρ := by
  simp only [physicalDepth,max_le_iff]
  constructor
  · rintro ⟨h₀,h₁,h₂⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0,h 1,h 2⟩

theorem physical_layer_eq_coordinateLayer (R ρ : ℝ) :
    {k ∈ cube R | physicalDepth R k ≤ ρ} = coordinateLayer R ρ := by
  ext k
  change ((∀ i : Fin 3, |k i| ≤ R) ∧ physicalDepth R k ≤ ρ) ↔
    ∀ i : Fin 3, |k i| ≤ R ∧ R-ρ ≤ |k i|
  rw [physicalDepth_le_iff]
  constructor
  · rintro ⟨hc,hd⟩ i
    exact ⟨hc i,by linarith [hd i]⟩
  · intro h
    exact ⟨fun i => (h i).1,fun i => by linarith [(h i).2]⟩

theorem physical_layer_volume_le (R ρ : ℝ) :
    volume {k ∈ cube R | physicalDepth R k ≤ ρ} ≤ 8*(ENNReal.ofReal ρ)^3 := by
  rw [physical_layer_eq_coordinateLayer]
  exact coordinateLayer_volume_le R ρ

theorem cornerDepth_layer_subset {R : ℝ} (hR : 0 < R) (ρ : ℝ) :
    {k ∈ cube R | cornerDepth R k ≤ ρ} ⊆ coordinateLayer R (2*R*ρ) := by
  rintro k ⟨hk,hd⟩ i
  refine ⟨hk i,?_⟩
  have hi := (le_maxDeficit (cornerCoordinates R k) i).trans hd
  change (R-|k i|)/(2*R) ≤ ρ at hi
  have hi' := (div_le_iff₀ (show 0 < 2*R by positivity)).mp hi
  nlinarith

theorem cornerDepth_layer_volume_le {R : ℝ} (hR : 0 < R) (ρ : ℝ) :
    volume {k ∈ cube R | cornerDepth R k ≤ ρ} ≤
      8*(ENNReal.ofReal (2*R*ρ))^3 :=
  (measure_mono (cornerDepth_layer_subset hR ρ)).trans (coordinateLayer_volume_le R (2*R*ρ))

theorem cornerDepth_zero_volume {R : ℝ} (hR : 0 < R) :
    volume {k ∈ cube R | cornerDepth R k = 0} = 0 := by
  apply le_antisymm _ (zero_le _)
  have h := cornerDepth_layer_volume_le hR 0
  simp only [mul_zero,ENNReal.ofReal_zero,zero_pow (by decide : 3 ≠ 0)] at h
  exact (measure_mono (by intro k hk; exact ⟨hk.1,hk.2.le⟩)).trans h

end
end Resonance.CornerLayerVolume

#check Resonance.CornerLayerVolume.edgeIntervals_volume_le
#print axioms Resonance.CornerLayerVolume.edgeIntervals_volume_le
#check Resonance.CornerLayerVolume.coordinate_mem_edgeIntervals
#print axioms Resonance.CornerLayerVolume.coordinate_mem_edgeIntervals
#check Resonance.CornerLayerVolume.coordinateLayer_measurable
#print axioms Resonance.CornerLayerVolume.coordinateLayer_measurable
#check Resonance.CornerLayerVolume.coordinateLayer_preimage_subset
#print axioms Resonance.CornerLayerVolume.coordinateLayer_preimage_subset
#check Resonance.CornerLayerVolume.coordinateLayer_volume_le
#print axioms Resonance.CornerLayerVolume.coordinateLayer_volume_le
#check Resonance.CornerLayerVolume.physicalDepth_le_iff
#print axioms Resonance.CornerLayerVolume.physicalDepth_le_iff
#check Resonance.CornerLayerVolume.physical_layer_eq_coordinateLayer
#print axioms Resonance.CornerLayerVolume.physical_layer_eq_coordinateLayer
#check Resonance.CornerLayerVolume.physical_layer_volume_le
#print axioms Resonance.CornerLayerVolume.physical_layer_volume_le
#check Resonance.CornerLayerVolume.cornerDepth_layer_subset
#print axioms Resonance.CornerLayerVolume.cornerDepth_layer_subset
#check Resonance.CornerLayerVolume.cornerDepth_layer_volume_le
#print axioms Resonance.CornerLayerVolume.cornerDepth_layer_volume_le
#check Resonance.CornerLayerVolume.cornerDepth_zero_volume
#print axioms Resonance.CornerLayerVolume.cornerDepth_zero_volume
