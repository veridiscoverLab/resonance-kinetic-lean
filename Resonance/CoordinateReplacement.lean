import Resonance.PinnedMeasure
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-! A genuine local coordinate replacement in the original Euclidean ambient
space.  The nonzero partial derivative is used to prove invertibility rather
than postulating a chart or a Jacobian. -/
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Resonance.CoordinateReplacement
noncomputable section
open PinnedMeasure

def unit (i : Fin 3) : Ambient := PiLp.single 2 i 1

def replace (i : Fin 3) (F : Ambient → ℝ) (p : Ambient) : Ambient :=
  p + (F p - p i) • unit i

def replaceDerivative (i : Fin 3) (L : Ambient →L[ℝ] ℝ) : Ambient →L[ℝ] Ambient :=
  ContinuousLinearMap.id ℝ Ambient + (L-coordinateProjection i).smulRight (unit i)

theorem replace_apply (i j : Fin 3) (F : Ambient → ℝ) (p : Ambient) :
    replace i F p j = if j=i then F p else p j := by
  by_cases h : j=i <;> simp [replace, unit, h]

theorem replaceDerivative_apply (i j : Fin 3) (L : Ambient →L[ℝ] ℝ) (p : Ambient) :
    replaceDerivative i L p j = if j=i then L p else p j := by
  by_cases h : j=i <;>
    simp [replaceDerivative, unit, h, coordinateProjection]

theorem replace_hasFDerivAt {F : Ambient → ℝ} {p : Ambient}
    {L : Ambient →L[ℝ] ℝ} (hF : HasFDerivAt F L p) (i : Fin 3) :
    HasFDerivAt (replace i F) (replaceDerivative i L) p := by
  exact (hasFDerivAt_id p).add ((hF.sub (coordinateProjection i).hasFDerivAt).smul_const (unit i))

theorem replace_contDiffAt {F : Ambient → ℝ} {p : Ambient}
    (hF : ContDiffAt ℝ 1 F p) (i : Fin 3) : ContDiffAt ℝ 1 (replace i F) p := by
  exact contDiffAt_id.add ((hF.sub (coordinateProjection i).contDiff.contDiffAt).smul contDiffAt_const)

theorem replaceDerivative_injective (i : Fin 3) (L : Ambient →L[ℝ] ℝ)
    (hL : L (unit i) ≠ 0) : Function.Injective (replaceDerivative i L) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  have hpi : ∀ j, j≠i → p j=0 := by
    intro j hj
    have h := congrArg (fun x : Ambient => x j) hp
    change replaceDerivative i L p j=0 at h
    simpa only [replaceDerivative_apply, if_neg hj, PiLp.zero_apply] using h
  have he : p = p i • unit i := by
    ext j
    by_cases hj : j=i
    · simp [unit, hj]
    · simp [unit, hj, hpi j hj]
  have hzero : L p=0 := by
    have h := congrArg (fun x : Ambient => x i) hp
    change replaceDerivative i L p i=0 at h
    simpa only [replaceDerivative_apply, if_pos rfl, PiLp.zero_apply] using h
  rw [he, map_smul, smul_eq_mul] at hzero
  have hscalar : p i=0 := (mul_eq_zero.mp hzero).resolve_right hL
  rw [he, hscalar, zero_smul]

theorem replaceDerivative_det (i : Fin 3) (L : Ambient →L[ℝ] ℝ) :
    (replaceDerivative i L).toLinearMap.det = L (unit i) := by
  rw [←LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3))]
  simp only [Matrix.det_fin_three, LinearMap.toMatrix_apply, PiLp.basisFun_repr,
    PiLp.basisFun_apply]
  fin_cases i <;> simp [replaceDerivative, unit, coordinateProjection]

theorem local_coordinate_exists {F : Ambient → ℝ} {p : Ambient}
    (hF : ContDiffAt ℝ 1 F p) (i : Fin 3)
    (hn : (fderiv ℝ F p) (unit i) ≠ 0) :
    ∃ e : OpenPartialHomeomorph Ambient Ambient,
      (e : Ambient → Ambient)=replace i F ∧ p∈e.source ∧
      ContDiffAt ℝ 1 e.symm (e p) := by
  let L := replaceDerivative i (fderiv ℝ F p)
  have hi : Function.Injective L := replaceDerivative_injective i _ hn
  let E : Ambient ≃L[ℝ] Ambient :=
    (LinearEquiv.ofBijective L.toLinearMap
      ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt (replace i F) (E : Ambient →L[ℝ] Ambient) p :=
    replace_hasFDerivAt (hF.differentiableAt (by norm_num)).hasFDerivAt i
  have hc := replace_contDiffAt hF i
  let e := hc.toOpenPartialHomeomorph (replace i F) hd (by norm_num)
  refine ⟨e, rfl, hc.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_⟩
  exact hc.to_localInverse hd (by norm_num)

theorem exact_volume_change (i : Fin 3) {F : Ambient → ℝ}
    {S : Set Ambient} (hS : MeasurableSet S)
    (hF : ∀p∈S, DifferentiableAt ℝ F p) (hi : InjOn (replace i F) S)
    (B : Ambient → ℝ≥0∞) :
    (∫⁻q in replace i F '' S, B q) =
      ∫⁻p in S, ENNReal.ofReal |(fderiv ℝ F p) (unit i)| * B (replace i F p) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun p hp => (replace_hasFDerivAt (hF p hp).hasFDerivAt i).hasFDerivWithinAt) hi B
  simpa only [replaceDerivative_det] using h

theorem exact_inverse_volume_change (i : Fin 3) {F : Ambient → ℝ}
    {S : Set Ambient} (hS : MeasurableSet S)
    (hF : ∀p∈S, DifferentiableAt ℝ F p) (hi : InjOn (replace i F) S)
    (hn : ∀p∈S, (fderiv ℝ F p) (unit i)≠0)
    (g : Ambient → Ambient) (hg : ∀p∈S, g (replace i F p)=p)
    (B : Ambient → ℝ≥0∞) :
    (∫⁻p in S, B p) = ∫⁻q in replace i F '' S,
      (ENNReal.ofReal |(fderiv ℝ F (g q)) (unit i)|)⁻¹ * B (g q) := by
  rw [exact_volume_change i hS hF hi]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  rw [hg p hp, ←mul_assoc,
    ENNReal.mul_inv_cancel (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr (hn p hp))))
      ENNReal.ofReal_ne_top, one_mul]

end
end Resonance.CoordinateReplacement
