import Resonance.NormalizedCornerStrips
import Resonance.OppositeSameCornerMass
import Resonance.CornerLayerVolume

/-! The full eight-corner layer is split by the original geometric
position of each leg; no independent collision roles are introduced. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.CornerRoleGeometry
noncomputable section
open ResonantMeasure CornerLayerVolume OppositeCornerBox NormalizedCornerStrips
set_option maxHeartbeats 1200000

def legLayer (R ρ : ℝ) (l : Fin 4) : Set FourMomenta :=
  {q | q l∈coordinateLayer R ρ}

def wrongUpperLayer (R ρ : ℝ) (l : Fin 4) : Set FourMomenta :=
  {q | q l∈coordinateLayer R ρ ∧ q l∉upperCorner R ρ}

theorem legLayer_measurable (R ρ : ℝ) (l : Fin 4) : MeasurableSet (legLayer R ρ l) :=
  (coordinateLayer_measurable R ρ).preimage (by fun_prop)

theorem wrongUpperLayer_measurable (R ρ : ℝ) (l : Fin 4) :
    MeasurableSet (wrongUpperLayer R ρ l) :=
  (legLayer_measurable R ρ l).inter ((upperCorner_measurable R ρ).preimage (by fun_prop)).compl

theorem corner_split (R ρ : ℝ) {p : E} (hp : p∈coordinateLayer R ρ) :
    p∈upperCorner R ρ ∨ ∃i:Fin 3,p i∈Icc (-R) (-R+ρ) := by
  classical
  by_cases hu : p∈upperCorner R ρ
  · exact Or.inl hu
  · right
    by_contra h
    apply hu
    intro i
    rcases coordinate_mem_edgeIntervals (hp i).1 (hp i).2 with hl|hr
    · exact False.elim (h ⟨i,hl⟩)
    · exact hr

theorem wrongUpperLayer_subset (R ρ : ℝ) (l : Fin 4) :
    wrongUpperLayer R ρ l ⊆ ⋃i:Fin 3,lowerFace R ρ l i := by
  intro q hq
  obtain ⟨i,hi⟩ := (corner_split R ρ hq.1).resolve_left hq.2
  exact mem_iUnion.mpr ⟨i,hi⟩

theorem oppositeLayer_subset (R ρ : ℝ) :
    legLayer R ρ 1 ⊆ oppositeCorner R ρ ∪ ⋃i:Fin 3,lowerFace R ρ 1 i := by
  intro q hq
  rcases corner_split R ρ hq with hu|⟨i,hi⟩
  · exact Or.inl hu
  · exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)

theorem finite_axis_mass_bound (μ : Measure FourMomenta) (R ρ : ℝ) (l : Fin 4) (B : ℝ≥0∞)
    (hb : ∀i:Fin 3,μ (lowerFace R ρ l i) ≤ B) :
    μ (⋃i:Fin 3,lowerFace R ρ l i) ≤ 3*B := by
  apply (measure_iUnion_fintype_le μ _).trans
  exact (Finset.sum_le_sum (fun i _ => hb i)).trans_eq (by simp)

end
end Resonance.CornerRoleGeometry
