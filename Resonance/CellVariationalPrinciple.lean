import Resonance.CellResponse
import Resonance.BoundedCellSource

/-! The original weak cell has a compact-parameter uniform H_nu bound
and is the unique maximizer of the actual dissipative response functional. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CellVariationalPrinciple
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalMomentProjection
open PhysicalVariationalCell CellResponse BoundedCellSource ReferenceMomentFunctionals

theorem actual_weak_cell_uniform_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀θ (hθ : θ∈K),∀(F : E→ℝ)
      (hF : MemLp F ∞ (referenceMeasure R)) (M : ℝ),0≤M →
      (∀ᵐk∂referenceMeasure R,‖F k‖≤M) → ‖cell hR (hpos hθ) hF‖≤C*M := by
  obtain ⟨C,hC,hb⟩ := solve_uniform_bound hR hK hpos
  refine ⟨C*(1+‖inverseVector hR‖),mul_pos hC (by positivity),?_⟩
  intro θ hθ F hF M hM hFM
  calc
    ‖cell hR (hpos hθ) hF‖ ≤ C*‖moment hR hF‖ := hb θ hθ _
    _ ≤ C*(‖inverseVector hR‖*M) :=
      mul_le_mul_of_nonneg_left (source_norm_bound hR hF hM hFM) hC.le
    _ ≤ C*(1+‖inverseVector hR‖)*M := by nlinarith [norm_nonneg (inverseVector hR)]

theorem micro_form_zero_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Micro hR hθ) :
    physicalForm hR.le hθ u u=0 ↔ u=0 := by
  constructor
  · intro hz
    obtain ⟨δ,hδ,hgap⟩ := actual_microBilin_coercive hR hθ
    have hg := hgap u
    change δ*‖u‖*‖u‖≤physicalForm hR.le hθ u u at hg
    rw [hz] at hg
    apply norm_eq_zero.mp
    by_contra hn
    have hp := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hn)
    exact (not_lt_of_ge hg) (mul_pos (mul_pos hδ hp) hp)
  · rintro rfl
    simp only [Submodule.coe_zero,physicalForm,map_zero,inner_zero_left]

def objective {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : Space R→L[ℝ]ℝ) (v : Micro hR hθ) : ℝ :=
  2*s v-physicalForm hR.le hθ v v

theorem complete_square {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : Space R→L[ℝ]ℝ) (v : Micro hR hθ) :
    objective hR hθ s v=response hR hθ s s-
      physicalForm hR.le hθ (v-solve hR hθ s) (v-solve hR hθ s) := by
  rw [objective,response_as_form,←solve_micro_pairing hR hθ s v]
  unfold physicalForm
  simp only [map_sub,inner_sub_left,inner_sub_right]
  rw [real_inner_comm (physicalDifference hR.le hθ v)
    (physicalDifference hR.le hθ (solve hR hθ s))]
  ring

theorem unique_variational_maximizer {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : Space R→L[ℝ]ℝ) (v : Micro hR hθ) :
    objective hR hθ s v≤response hR hθ s s ∧
      (objective hR hθ s v=response hR hθ s s ↔ v=solve hR hθ s) := by
  have hn : 0≤physicalForm hR.le hθ (v-solve hR hθ s) (v-solve hR hθ s) := by
    unfold physicalForm
    rw [real_inner_self_eq_norm_sq]
    positivity
  rw [complete_square]
  refine ⟨sub_le_self _ hn,?_⟩
  rw [sub_eq_self]
  exact (micro_form_zero_iff hR hθ (v-solve hR hθ s)).trans sub_eq_zero

end
end Resonance.CellVariationalPrinciple
