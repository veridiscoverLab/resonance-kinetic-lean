import Resonance.PhysicalVariationalCell

/-! Uniform weak-cell bounds and the response bilinear form of the actual
four-leg operator. All inverses are the constructed variational inverse. -/
namespace Resonance.CellResponse
noncomputable section
open Set ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalMomentProjection
open PhysicalVariationalCell

theorem physicalForm_symmetric {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v : Space R) :
    physicalForm hR.le hθ u v=physicalForm hR.le hθ v u := real_inner_comm _ _

theorem physicalForm_add_left {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v w : Space R) :
    physicalForm hR.le hθ (u+v) w=
      physicalForm hR.le hθ u w+physicalForm hR.le hθ v w := by
  unfold physicalForm
  rw [map_add,inner_add_left]

theorem physicalForm_smul_left {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : ℝ) (u v : Space R) :
    physicalForm hR.le hθ (a • u) v=a*physicalForm hR.le hθ u v := by
  unfold physicalForm
  rw [map_smul,real_inner_smul_left]

theorem solve_add {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (s t : Space R→L[ℝ]ℝ) : solve hR hθ (s+t)=solve hR hθ s+solve hR hθ t := by
  symm
  apply solve_unique hR hθ
  intro v
  change physicalForm hR.le hθ ((solve hR hθ s : Space R)+(solve hR hθ t : Space R)) v=_
  rw [physicalForm_add_left hR hθ,solve_micro_pairing,solve_micro_pairing]
  rfl

theorem solve_smul {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (a : ℝ) (s : Space R→L[ℝ]ℝ) : solve hR hθ (a • s)=a • solve hR hθ s := by
  symm
  apply solve_unique hR hθ
  intro v
  change physicalForm hR.le hθ (a • (solve hR hθ s : Space R)) v=_
  rw [physicalForm_smul_left hR hθ,solve_micro_pairing]
  rfl

theorem solve_uniform_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀θ (hθ : θ∈K),∀s : Space R→L[ℝ]ℝ,
      ‖solve hR (hpos hθ) s‖≤C*‖s‖ := by
  obtain ⟨δ,C,hδ,_hC,hgap⟩ := PhysicalMicroCoercivity.actual_microcoercivity hR hK hpos
  refine ⟨δ⁻¹,inv_pos.mpr hδ,?_⟩
  intro θ hθ s
  let u := solve hR (hpos hθ) s
  have hg := (hgap θ hθ u u.property).1
  have he := solve_micro_pairing hR (hpos hθ) s u
  have hle : δ*‖u‖^2≤‖s‖*‖u‖ := by
    calc
      _ ≤ physicalForm hR.le (hpos hθ) u u := hg
      _ = s (u : Space R) := he
      _ ≤ ‖s (u : Space R)‖ := le_abs_self _
      _ ≤ ‖s‖*‖u‖ := s.le_opNorm u
  by_cases hu : ‖u‖=0
  · change ‖u‖≤δ⁻¹*‖s‖
    rw [hu]
    positivity
  · have hnorm : 0<‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
    have hh : δ*‖u‖≤‖s‖ := (mul_le_mul_iff_left₀ hnorm).mp (by
      simpa only [pow_two,mul_assoc] using hle)
    change ‖u‖≤δ⁻¹*‖s‖
    exact (le_inv_mul_iff₀ hδ).mpr hh

def response {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (s t : Space R→L[ℝ]ℝ) : ℝ := s (solve hR hθ t)

theorem response_as_form {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s t : Space R→L[ℝ]ℝ) :
    response hR hθ s t=physicalForm hR.le hθ (solve hR hθ s) (solve hR hθ t) :=
  (solve_micro_pairing hR hθ s (solve hR hθ t)).symm

theorem response_symmetric {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s t : Space R→L[ℝ]ℝ) :
    response hR hθ s t=response hR hθ t s := by
  rw [response_as_form,response_as_form,physicalForm_symmetric hR hθ]

theorem response_nonnegative {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : Space R→L[ℝ]ℝ) : 0≤response hR hθ s s := by
  rw [response_as_form]
  change 0 ≤ inner ℝ _ _
  rw [real_inner_self_eq_norm_sq]
  positivity

theorem response_zero_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : Space R→L[ℝ]ℝ) :
    response hR hθ s s=0 ↔ solve hR hθ s=0 := by
  constructor
  · intro hz
    obtain ⟨δ,hδ,hgap⟩ := actual_microBilin_coercive hR hθ
    have hg := hgap (solve hR hθ s)
    change δ*‖solve hR hθ s‖*‖solve hR hθ s‖≤
      physicalForm hR.le hθ (solve hR hθ s) (solve hR hθ s) at hg
    rw [←response_as_form,hz] at hg
    have hn : ‖solve hR hθ s‖=0 := by
      by_contra hn
      have hp := lt_of_le_of_ne (norm_nonneg (solve hR hθ s)) (Ne.symm hn)
      exact (not_lt_of_ge hg) (mul_pos (mul_pos hδ hp) hp)
    exact norm_eq_zero.mp hn
  · intro hz
    simp only [response,hz,Submodule.coe_zero,map_zero]

end
end Resonance.CellResponse
