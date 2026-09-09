import Resonance.ActualSobolevReality

/-! The closed real Sobolev subspace and the restricted positive-time
semigroup. The closedness and strong continuity are consequences of the
actual Fourier decoding, not additional hypotheses. -/
open Set
open scoped NNReal
namespace Resonance.ActualRealSobolev
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualSobolevSpace ActualSobolevReality
open ActualSobolevSemigroup ActualFourierReality PhysicalScalarFourier ActualGramHilbert

theorem coefficient_continuous {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (n : Frequency) :
    Continuous (fun v:Sobolev s=>coefficient hR hθ s v n) :=
  ((inverseOperator R θ).continuous.comp
    ((continuous_apply n).comp lp.uniformContinuous_coe.continuous)).const_smul _

theorem real_condition_closed {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) : IsClosed {v:Sobolev s|IsReal hR hθ s v} := by
  have hh := isClosed_iInter (fun n=>isClosed_eq (coefficient_continuous hR hθ s (-n))
    (conjugation.continuous.comp (coefficient_continuous hR hθ s n)))
  convert hh using 1
  ext v
  simp [IsReal]

def realSubspace {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (s : ℝ) : Submodule ℝ (Sobolev s) where
  carrier:= {v|IsReal hR hθ s v}
  zero_mem':=by
    intro n
    change (((weight s (-n))⁻¹:ℝ):ℂ) • inverseOperator R θ (0:H)=
      conjugation ((((weight s n)⁻¹:ℝ):ℂ) • inverseOperator R θ (0:H))
    simp
  add_mem' hv hw:=by
    intro n
    simp only [coefficient,lp.coeFn_add,Pi.add_apply,map_add,smul_add]
    exact congrArg₂ (·+·) (hv n) (hw n)
  smul_mem' a v hv:=by
    intro n
    have hc : ∀m:Frequency,coefficient hR hθ s (a • v) m=a • coefficient hR hθ s v m := by
      intro m
      unfold coefficient
      change (((weight s m)⁻¹:ℝ):ℂ) • inverseOperator R θ ((a:ℂ) • v m)=
        (a:ℂ) • ((((weight s m)⁻¹:ℝ):ℂ) • inverseOperator R θ (v m))
      rw [map_smul,smul_comm]
    rw [hc,hc,map_smul,hv n]

instance realSubspace_complete {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) : CompleteSpace (realSubspace hR hθ s) :=
  (real_condition_closed hR hθ s).completeSpace_coe

def realEvolution {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {c : ℝ} (hc : 0<c) (s : ℝ) (t : ℝ≥0) (v : realSubspace hR hθ s) :
    realSubspace hR hθ s :=
  ⟨evolution hR hθ hc s t v,evolution_preserves_real hR hθ hc s t v v.property⟩

theorem realEvolution_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ)
    (v : realSubspace hR hθ s) : realEvolution hR hθ hc s 0 v=v := by
  apply Subtype.ext
  exact DFunLike.congr_fun (evolution_zero hR hθ hc s) v.val

theorem realEvolution_add {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ) (t u : ℝ≥0)
    (v : realSubspace hR hθ s) :
    realEvolution hR hθ hc s (t+u) v=
      realEvolution hR hθ hc s t (realEvolution hR hθ hc s u v) := by
  apply Subtype.ext
  exact DFunLike.congr_fun (evolution_add hR hθ hc s t u) v.val

theorem realEvolution_strong_continuous {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ)
    (v : realSubspace hR hθ s) : Continuous (fun t:ℝ≥0=>realEvolution hR hθ hc s t v) :=
  (evolution_strong_continuous hR hθ hc s v.val).subtype_mk _

set_option backward.isDefEq.respectTransparency false in
def realEvolutionOperator {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ) (t : ℝ≥0) :
    realSubspace hR hθ s→L[ℝ]realSubspace hR hθ s :=
  (((evolution hR hθ hc s t).restrictScalars ℝ).comp (realSubspace hR hθ s).subtypeL).codRestrict
    (realSubspace hR hθ s) (fun v=>evolution_preserves_real hR hθ hc s t v v.property)

theorem realEvolutionOperator_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ) (t : ℝ≥0)
    (v : realSubspace hR hθ s) :
    realEvolutionOperator hR hθ hc s t v=realEvolution hR hθ hc s t v := rfl

set_option backward.isDefEq.respectTransparency false in
theorem realEvolutionOperator_norm {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ) (t : ℝ≥0) :
    ‖realEvolutionOperator hR hθ hc s t‖≤Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 3)
  intro v
  have hh := (evolution hR hθ hc s t).le_opNorm v.val
  have hb := mul_le_mul_of_nonneg_right (evolution_norm hR hθ hc s t) (norm_nonneg v.val)
  exact hh.trans hb

end
end Resonance.ActualRealSobolev
