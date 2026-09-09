import Resonance.PhysicalMarginal
import Resonance.CollisionForm

/-! The complete pairing form as a bounded operator on the original sharp-cube
Lebesgue L² space.  The pointwise nonlinear collision derivative and its RJ
weighted version are distinct subsequent identifications. -/
open MeasureTheory
open scoped ENNReal NNReal

namespace Resonance.PhysicalCollisionForm
noncomputable section
open ResonantMeasure PhysicalMarginal

abbrev H (R : ℝ) := Lp ℝ 2 (physicalMeasure R)
abbrev J (R : ℝ) := Lp ℝ 2 (pairingMeasure R)

theorem marginal_ac_physical {R : ℝ} (hR : 0 ≤ R) :
    CollisionForm.marginal R ≪ physicalMeasure R :=
  Measure.absolutelyContinuous_of_le_smul (cube_marginal_domination hR 0)

def inclusion {R : ℝ} (hR : 0 ≤ R) (f : H R) : CollisionForm.H R :=
  ((Lp.memLp f).of_measure_le_smul (marginalConstant_finite R).ne
    (cube_marginal_domination hR 0)).toLp f

theorem inclusion_ae {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    inclusion hR f =ᵐ[CollisionForm.marginal R] f := MemLp.coeFn_toLp _

theorem inclusion_add {R : ℝ} (hR : 0 ≤ R) (f g : H R) :
    inclusion hR (f + g) = inclusion hR f + inclusion hR g := by
  apply Lp.ext
  filter_upwards [inclusion_ae hR (f+g), inclusion_ae hR f, inclusion_ae hR g,
    Lp.coeFn_add (inclusion hR f) (inclusion hR g),
    (marginal_ac_physical hR).ae_eq (Lp.coeFn_add f g)] with x hfg hf hg hsum hin
  simp only [Pi.add_apply] at hsum hin
  rw [hfg, hsum, hin, hf, hg]

theorem inclusion_smul {R : ℝ} (hR : 0 ≤ R) (a : ℝ) (f : H R) :
    inclusion hR (a • f) = a • inclusion hR f := by
  apply Lp.ext
  filter_upwards [inclusion_ae hR (a • f), inclusion_ae hR f,
    Lp.coeFn_smul a (inclusion hR f),
    (marginal_ac_physical hR).ae_eq (Lp.coeFn_smul a f)] with x haf hf hs hin
  simp only [Pi.smul_apply] at hs hin
  rw [haf, hs, hin, hf]

def inclusionNorm (R : ℝ) : ℝ := ((marginalConstant R) ^ (1 / 2 : ℝ)).toReal

theorem inclusion_bound {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    ‖inclusion hR f‖ ≤ inclusionNorm R * ‖f‖ := by
  have hmono := eLpNorm_mono_measure (p := 2) f (cube_marginal_domination hR 0)
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at hmono
  norm_num at hmono
  have htop : marginalConstant R ^ (1 / 2 : ℝ) *
      eLpNorm f 2 (physicalMeasure R) < ∞ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (marginalConstant_finite R).ne) (Lp.memLp f).2
  have ht := ENNReal.toReal_mono htop.ne hmono
  rw [ENNReal.toReal_mul] at ht
  unfold inclusion
  rw [Lp.norm_toLp]
  exact ht

def inclusionLinear {R : ℝ} (hR : 0 ≤ R) : H R →ₗ[ℝ] CollisionForm.H R where
  toFun := inclusion hR
  map_add' := inclusion_add hR
  map_smul' := inclusion_smul hR

def inclusionCLM {R : ℝ} (hR : 0 ≤ R) : H R →L[ℝ] CollisionForm.H R :=
  (inclusionLinear hR).mkContinuous (inclusionNorm R) (inclusion_bound hR)

def fullDifference {R : ℝ} (hR : 0 ≤ R) : H R →L[ℝ] J R :=
  (CollisionForm.fullDifference R).comp (inclusionCLM hR)

theorem fullDifference_ae {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    fullDifference hR f =ᵐ[pairingMeasure R] completeDifference f := by
  have h (i : Fin 4) := (CollisionForm.all_legs_preserve R i).quasiMeasurePreserving.ae_eq
    (inclusion_ae hR f)
  filter_upwards [CollisionForm.fullDifference_ae R (inclusion hR f), h 0, h 1, h 2, h 3]
    with k hd h0 h1 h2 h3
  change CollisionForm.fullDifference R (inclusion hR f) k = _
  rw [hd]
  dsimp only [CollisionForm.rawDifference, completeDifference, Function.comp_def] at *
  rw [h0, h1, h2, h3]

theorem fullDifference_bound {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    ‖fullDifference hR f‖ ≤ (2 * inclusionNorm R) * ‖f‖ := by
  exact (CollisionForm.fullDifference_bound R (inclusion hR f)).trans
    (by nlinarith [inclusion_bound hR f])

def fullOperator {R : ℝ} (hR : 0 ≤ R) : H R →L[ℝ] H R :=
  (fullDifference hR).adjoint.comp (fullDifference hR)

theorem fullOperator_pairing {R : ℝ} (hR : 0 ≤ R) (f g : H R) :
    inner ℝ f (fullOperator hR g) = inner ℝ (fullDifference hR f) (fullDifference hR g) :=
  ContinuousLinearMap.adjoint_inner_right (fullDifference hR) f (fullDifference hR g)

theorem fullOperator_nonneg {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    0 ≤ inner ℝ f (fullOperator hR f) := by
  rw [fullOperator_pairing, real_inner_self_eq_norm_sq]
  positivity

theorem fullOperator_selfAdjoint {R : ℝ} (hR : 0 ≤ R) : IsSelfAdjoint (fullOperator hR) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  simp [fullOperator, ContinuousLinearMap.adjoint_comp]

theorem fullOperator_integral {R : ℝ} (hR : 0 ≤ R) (f g : H R) :
    inner ℝ f (fullOperator hR g) =
      ∫ k, completeDifference f k * completeDifference g k ∂pairingMeasure R := by
  rw [fullOperator_pairing, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fullDifference_ae hR f, fullDifference_ae hR g] with k hf hg
  rw [hf, hg]
  change completeDifference g k * completeDifference f k = _
  ring

theorem fullOperator_kernel {R : ℝ} (hR : 0 ≤ R) :
    (fullOperator hR).ker = (fullDifference hR).ker :=
  ContinuousLinearMap.ker_adjoint_comp_self (fullDifference hR)

theorem fullOperator_eq_zero_iff {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    fullOperator hR f = 0 ↔
      ∀ᵐ k ∂pairingMeasure R, f (k 0) + f (k 1) = f (k 2) + f (k 3) := by
  have hker : fullOperator hR f = 0 ↔ fullDifference hR f = 0 := by
    change f ∈ (fullOperator hR).ker ↔ f ∈ (fullDifference hR).ker
    rw [fullOperator_kernel]
  rw [hker]
  constructor
  · intro hf
    have ha := fullDifference_ae hR f
    rw [hf] at ha
    filter_upwards [ha, Lp.coeFn_zero ℝ 2 (pairingMeasure R)] with k hk hz
    have hr : completeDifference f k = 0 := by simpa using hk.symm.trans hz
    dsimp [completeDifference] at hr
    linarith
  · intro hf
    apply Lp.ext
    filter_upwards [fullDifference_ae hR f, hf, Lp.coeFn_zero ℝ 2 (pairingMeasure R)] with k hk hr hz
    rw [hk, hz]
    dsimp [completeDifference]
    linarith

theorem fullOperator_quadratic_eq_zero_iff {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    inner ℝ f (fullOperator hR f) = 0 ↔
      ∀ᵐ k ∂pairingMeasure R, f (k 0) + f (k 1) = f (k 2) + f (k 3) := by
  rw [fullOperator_pairing, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]
  have hker : fullDifference hR f = 0 ↔ fullOperator hR f = 0 := by
    change f ∈ (fullDifference hR).ker ↔ f ∈ (fullOperator hR).ker
    rw [fullOperator_kernel]
  rw [hker, fullOperator_eq_zero_iff]

theorem fullDifference_graph_closed {R : ℝ} (hR : 0 ≤ R) :
    IsClosed {p : H R × J R | p.2 = fullDifference hR p.1} :=
  isClosed_eq continuous_snd ((fullDifference hR).continuous.comp continuous_fst)

theorem maximal_form_domain {R : ℝ} (hR : 0 ≤ R) :
    {f : H R | MemLp (completeDifference f) 2 (pairingMeasure R)} = Set.univ := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact cube_difference_memLp hR (Lp.memLp f)

end
end Resonance.PhysicalCollisionForm
