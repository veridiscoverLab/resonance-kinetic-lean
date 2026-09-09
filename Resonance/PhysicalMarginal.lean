import Resonance.ResonantMeasure

/-! Uniform domination of the actual common pairing marginals by physical
Lebesgue volume.  The proof keeps the common center and all four sharp flags.
This is a bound for the concrete pairing measure, not an assumed collision kernel. -/
open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Resonance.PhysicalMarginal
noncomputable section
open ResonantMeasure

def radiusCeiling (R : ℝ) : Radius := ⟨3 * max R 0 + 1, by change 0 < 3 * max R 0 + 1; positivity⟩
def boundedOther (R : ℝ) : Measure (Radius × (Sphere × Sphere)) :=
  (radial.restrict (Iio (radiusCeiling R))).prod (surface.prod surface)
def boundedParameters (R : ℝ) : Measure Parameters :=
  (volume : Measure E).prod (boundedOther R)
def marginalConstant (R : ℝ) : ℝ≥0∞ := 2 * boundedOther R univ

theorem boundedOther_finite (R : ℝ) : IsFiniteMeasure (boundedOther R) := by
  have hr : radial (Iio (radiusCeiling R)) < ∞ := by
    rw [radial, Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (radial.restrict (Iio (radiusCeiling R))) :=
    ⟨by simpa using hr⟩
  unfold boundedOther
  infer_instance

theorem marginalConstant_finite (R : ℝ) : marginalConstant R < ∞ := by
  letI := boundedOther_finite R
  exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)

theorem boundedParameters_restrict (R : ℝ) :
    boundedParameters R =
      base.restrict (univ ×ˢ (Iio (radiusCeiling R) ×ˢ (univ : Set (Sphere × Sphere)))) := by
  have hi := Measure.prod_restrict (μ := radial) (ν := surface.prod surface)
    (Iio (radiusCeiling R)) univ
  have ho := Measure.prod_restrict (μ := (volume : Measure E))
    (ν := radial.prod (surface.prod surface)) univ
    (Iio (radiusCeiling R) ×ˢ (univ : Set (Sphere × Sphere)))
  simp only [Measure.restrict_univ] at hi ho
  change volume.prod ((radial.restrict (Iio (radiusCeiling R))).prod (surface.prod surface)) = _
  rw [hi]
  exact ho

theorem parameterMeasure_le_bounded {R : ℝ} (hR : 0 ≤ R) :
    parameterMeasure R ≤ (2 : ℝ≥0∞) • boundedParameters R := by
  rw [parameterMeasure, boundedParameters_restrict]
  have hsub : allowed R ⊆ univ ×ˢ
      (Iio (radiusCeiling R) ×ˢ (univ : Set (Sphere × Sphere))) := by
    intro p hp
    refine ⟨trivial, ?_, trivial⟩
    have hr := (parameter_bounds hR hp).2
    change (p.2.1 : ℝ) < 3 * max R 0 + 1
    rw [max_eq_left hR]
    linarith
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Measure.restrict_mono hsub le_rfl s) (zero_le _)

/-- Integrating any translation of one common Lebesgue center produces the
mass of the other variables times that same physical volume. -/
theorem map_center_translation {B : Type*} [MeasurableSpace B]
    (μ : Measure B) [IsFiniteMeasure μ] (shift : B → E) (hs : Measurable shift) :
    Measure.map (fun p : E × B => p.1 + shift p.2) ((volume : Measure E).prod μ) =
      (μ univ) • (volume : Measure E) := by
  have hm : Measurable (fun p : E × B => p.1 + shift p.2) := measurable_fst.add (hs.comp measurable_snd)
  apply Measure.ext
  intro s hset
  rw [Measure.map_apply hm hset, Measure.prod_apply_symm (hm hset)]
  have he (b : B) : (volume : Measure E)
      ((fun V : E => (V,b)) ⁻¹' ((fun p : E × B => p.1 + shift p.2) ⁻¹' s)) = volume s := by
    exact ((MeasurePreserving.id (volume : Measure E)).add_right volume (shift b)).measure_preimage
      hset.nullMeasurableSet
  simp_rw [he]
  simp [mul_comm]

theorem bounded_marginal (R : ℝ) (i : Fin 4) :
    Measure.map (fun p : Parameters => paired p i) (boundedParameters R) =
      (boundedOther R univ) • (volume : Measure E) := by
  letI := boundedOther_finite R
  simpa only [boundedParameters, paired_leg_translate] using
    map_center_translation (boundedOther R) (legShift i) (measurable_legShift i)

theorem physical_marginal_domination {R : ℝ} (hR : 0 ≤ R) (i : Fin 4) :
    Measure.map (fun k : FourMomenta => k i) (pairingMeasure R) ≤
      marginalConstant R • (volume : Measure E) := by
  rw [pairingMeasure, Measure.map_map (measurable_pi_apply i) continuous_paired.measurable]
  have hm : Measure.map (fun p : Parameters => paired p i) (parameterMeasure R) ≤
      Measure.map (fun p : Parameters => paired p i) ((2 : ℝ≥0∞) • boundedParameters R) :=
    Measure.map_mono (parameterMeasure_le_bounded hR)
      ((measurable_pi_apply i).comp continuous_paired.measurable)
  simpa only [Measure.map_smul, bounded_marginal, smul_smul, marginalConstant, Function.comp_def] using hm

theorem physical_leg_memLp {R : ℝ} (hR : 0 ≤ R) (i : Fin 4)
    {p : ℝ≥0∞} {f : E → ℝ} (hf : MemLp f p (volume : Measure E)) :
    MemLp (fun k : FourMomenta => f (k i)) p (pairingMeasure R) := by
  have hm := hf.of_measure_le_smul (marginalConstant_finite R).ne
    (physical_marginal_domination hR i)
  exact hm.comp_of_map (measurable_pi_apply i).aemeasurable

def completeDifference (f : E → ℝ) (k : FourMomenta) : ℝ :=
  (1 / 2 : ℝ) * (f (k 0) + f (k 1) - f (k 2) - f (k 3))

theorem physical_difference_memLp {R : ℝ} (hR : 0 ≤ R)
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) :
    MemLp (completeDifference f) 2 (pairingMeasure R) :=
  ((((physical_leg_memLp hR 0 hf).add (physical_leg_memLp hR 1 hf)).sub
    (physical_leg_memLp hR 2 hf)).sub (physical_leg_memLp hR 3 hf)).const_mul _

theorem physical_full_form_integrable {R : ℝ} (hR : 0 ≤ R)
    {f g : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (hg : MemLp g 2 (volume : Measure E)) :
    Integrable (fun k => completeDifference f k * completeDifference g k) (pairingMeasure R) :=
  (physical_difference_memLp hR hf).integrable_mul (physical_difference_memLp hR hg)

def physicalMeasure (R : ℝ) : Measure E := (volume : Measure E).restrict (cube R)

theorem marginal_supported_cube (R : ℝ) (i : Fin 4) :
    ∀ᵐ k ∂Measure.map (fun k : FourMomenta => k i) (pairingMeasure R), k ∈ cube R := by
  rw [ae_iff]
  change Measure.map (fun k : FourMomenta => k i) (pairingMeasure R) (cube R)ᶜ = 0
  rw [Measure.map_apply (measurable_pi_apply i) (measurable_cube R).compl]
  apply le_antisymm _ (zero_le _)
  apply le_trans (measure_mono ?_) (pairing_supported_on_fullResonance R).le
  intro k hk hfull
  exact hk (hfull.1 i)

theorem cube_marginal_domination {R : ℝ} (hR : 0 ≤ R) (i : Fin 4) :
    Measure.map (fun k : FourMomenta => k i) (pairingMeasure R) ≤
      marginalConstant R • physicalMeasure R := by
  have h := Measure.restrict_mono_measure (physical_marginal_domination hR i) (cube R)
  rw [Measure.restrict_eq_self_of_ae_mem (marginal_supported_cube R i),
    Measure.restrict_smul] at h
  exact h

theorem cube_leg_memLp {R : ℝ} (hR : 0 ≤ R) (i : Fin 4)
    {p : ℝ≥0∞} {f : E → ℝ} (hf : MemLp f p (physicalMeasure R)) :
    MemLp (fun k : FourMomenta => f (k i)) p (pairingMeasure R) := by
  have hm := hf.of_measure_le_smul (marginalConstant_finite R).ne
    (cube_marginal_domination hR i)
  exact hm.comp_of_map (measurable_pi_apply i).aemeasurable

theorem cube_difference_memLp {R : ℝ} (hR : 0 ≤ R)
    {f : E → ℝ} (hf : MemLp f 2 (physicalMeasure R)) :
    MemLp (completeDifference f) 2 (pairingMeasure R) :=
  ((((cube_leg_memLp hR 0 hf).add (cube_leg_memLp hR 1 hf)).sub
    (cube_leg_memLp hR 2 hf)).sub (cube_leg_memLp hR 3 hf)).const_mul _

theorem cube_full_form_integrable {R : ℝ} (hR : 0 ≤ R)
    {f g : E → ℝ} (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) :
    Integrable (fun k => completeDifference f k * completeDifference g k) (pairingMeasure R) :=
  (cube_difference_memLp hR hf).integrable_mul (cube_difference_memLp hR hg)

end
end Resonance.PhysicalMarginal
