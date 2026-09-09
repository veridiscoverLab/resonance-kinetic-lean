import Mathlib
import Resonance.ResonantMeasure
import Resonance.Thermodynamics

/-! Actual Cartesian pairing coordinates and radial energy change of variables.
No Dirac/coarea identity is inserted as a definition or assumption.
The global sharp energy-layer limit over all centers, radii and angles is not
asserted here; fixed-radius convergence is distinguished from that remaining bridge. -/
open MeasureTheory Set Metric Matrix
open scoped ENNReal NNReal Matrix Kronecker

namespace Resonance.CoareaNormalization
noncomputable section

abbrev Index := Fin 3 × Fin 3
abbrev Nine := Index → ℝ

def blockMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 0; 1, -1, 0; 1, 0, 1]

def coordinateMatrix : Matrix Index Index ℝ :=
  blockMatrix ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℝ)

def coordinateMap : Nine →ₗ[ℝ] Nine := Matrix.toLin' coordinateMatrix

theorem blockMatrix_det : Matrix.det blockMatrix = -2 := by
  rw [Matrix.det_fin_three]
  change (1 * (-1) * 1 - 1 * 0 * 0 - 1 * 1 * 1 +
    1 * 0 * 1 + 0 * 1 * 0 - 0 * (-1) * 1 : ℝ) = -2
  norm_num

theorem coordinateMatrix_det : Matrix.det coordinateMatrix = -8 := by
  rw [coordinateMatrix, Matrix.det_kronecker, blockMatrix_det]
  norm_num

theorem coordinateMap_zero (z : Nine) (j : Fin 3) :
    coordinateMap z (0, j) = z (0, j) + z (1, j) := by
  fin_cases j <;>
    simp [coordinateMap, coordinateMatrix, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, blockMatrix,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem coordinateMap_one (z : Nine) (j : Fin 3) :
    coordinateMap z (1, j) = z (0, j) - z (1, j) := by
  fin_cases j <;>
    simp [coordinateMap, coordinateMatrix, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, blockMatrix,
      Fin.sum_univ_succ, Matrix.one_apply, sub_eq_add_neg]

theorem coordinateMap_two (z : Nine) (j : Fin 3) :
    coordinateMap z (2, j) = z (0, j) + z (2, j) := by
  fin_cases j <;>
    simp [coordinateMap, coordinateMatrix, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, blockMatrix,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem coordinateMap_measurable : Measurable coordinateMap :=
  coordinateMap.continuous_of_finiteDimensional.measurable

theorem coordinateMap_volume :
    Measure.map coordinateMap (volume : Measure Nine) =
      ENNReal.ofReal (1 / 8 : ℝ) • (volume : Measure Nine) := by
  have hn : Matrix.det coordinateMatrix ≠ 0 := by rw [coordinateMatrix_det]; norm_num
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hn
  simpa [coordinateMap, coordinateMatrix_det] using hm

/-- The factor 8 is proved for the same arbitrary Cartesian readout, not inserted in a density. -/
theorem cartesian_integral_change (F : Nine → ℝ)
    (hF : AEStronglyMeasurable F (volume : Measure Nine)) :
    (∫ z, F z) = 8 * ∫ z, F (coordinateMap z) := by
  have hmap : AEStronglyMeasurable F (Measure.map coordinateMap (volume : Measure Nine)) := by
    rw [coordinateMap_volume]
    exact hF.smul_measure _
  have he := integral_map coordinateMap_measurable.aemeasurable hmap
  rw [coordinateMap_volume, integral_smul_measure] at he
  norm_num at he
  linarith

abbrev E := ResonantMeasure.E
abbrev FourMomenta := ResonantMeasure.FourMomenta

def momentumAt (z : Nine) (i : Fin 3) : E := WithLp.toLp 2 (fun j => z (i,j))

def physicalFour (z : Nine) : FourMomenta :=
  ![momentumAt z 0, momentumAt z 1, momentumAt z 2,
    momentumAt z 0 + momentumAt z 1 - momentumAt z 2]

def pairedFour (z : Nine) : FourMomenta :=
  ![momentumAt z 0 + momentumAt z 1, momentumAt z 0 - momentumAt z 1,
    momentumAt z 0 + momentumAt z 2, momentumAt z 0 - momentumAt z 2]

theorem coordinate_four_identity (z : Nine) :
    physicalFour (coordinateMap z) = pairedFour z := by
  have h0 : momentumAt (coordinateMap z) 0 = momentumAt z 0 + momentumAt z 1 := by
    ext j
    exact coordinateMap_zero z j
  have h1 : momentumAt (coordinateMap z) 1 = momentumAt z 0 - momentumAt z 1 := by
    ext j
    exact coordinateMap_one z j
  have h2 : momentumAt (coordinateMap z) 2 = momentumAt z 0 + momentumAt z 2 := by
    ext j
    exact coordinateMap_two z j
  funext i
  fin_cases i <;> simp [physicalFour, pairedFour, h0, h1, h2]

/-- Every whole-four-leg test is transported through the actual Jacobian identity. -/
theorem four_leg_integral_change (Φ : FourMomenta → ℝ)
    (hΦ : AEStronglyMeasurable (fun z => Φ (physicalFour z)) (volume : Measure Nine)) :
    (∫ z, Φ (physicalFour z)) = 8 * ∫ z, Φ (pairedFour z) := by
  simpa only [coordinate_four_identity] using
    cartesian_integral_change (fun z => Φ (physicalFour z)) hΦ

theorem paired_energy_difference (z : Nine) :
    ‖pairedFour z 0‖ ^ 2 + ‖pairedFour z 1‖ ^ 2 -
      ‖pairedFour z 2‖ ^ 2 - ‖pairedFour z 3‖ ^ 2 =
        2 * (‖momentumAt z 1‖ ^ 2 - ‖momentumAt z 2‖ ^ 2) := by
  change ‖momentumAt z 0 + momentumAt z 1‖ ^ 2 +
    ‖momentumAt z 0 - momentumAt z 1‖ ^ 2 -
    ‖momentumAt z 0 + momentumAt z 2‖ ^ 2 -
    ‖momentumAt z 0 - momentumAt z 2‖ ^ 2 = _
  have hp := parallelogram_law_with_norm ℝ (momentumAt z 0) (momentumAt z 1)
  have hq := parallelogram_law_with_norm ℝ (momentumAt z 0) (momentumAt z 2)
  linarith

/-- The actual radial energy before imposing its zero level. -/
def radialEnergy (r s : ℝ) : ℝ := 2 * (r ^ 2 - s ^ 2)

def energyRadius (r e : ℝ) : ℝ := Real.sqrt (r ^ 2 - e / 2)

theorem radialEnergy_derivative (r s : ℝ) :
    HasDerivAt (radialEnergy r) (-4 * s) s := by
  unfold radialEnergy
  convert (((hasDerivAt_const s (r ^ 2)).sub ((hasDerivAt_id s).pow 2)).const_mul 2) using 1
  · simp only [id_eq]
    ring

theorem radialEnergy_injective (r : ℝ) : Set.InjOn (radialEnergy r) (Ioi 0) := by
  intro x hx y hy he
  dsimp [radialEnergy] at he
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  nlinarith

theorem energyRadius_of_energy (r : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    energyRadius r (radialEnergy r s) = s := by
  unfold energyRadius radialEnergy
  have he : r ^ 2 - 2 * (r ^ 2 - s ^ 2) / 2 = s ^ 2 := by ring
  rw [he, Real.sqrt_sq hs]

theorem radialEnergy_image (r : ℝ) :
    radialEnergy r '' Ioi 0 = Iio (2 * r ^ 2) := by
  ext e
  constructor
  · rintro ⟨s, hs, rfl⟩
    change 2 * (r ^ 2 - s ^ 2) < 2 * r ^ 2
    have hspos : 0 < s := hs
    nlinarith [sq_pos_of_pos hspos]
  · intro he
    have hp : 0 < r ^ 2 - e / 2 := by
      change e < 2 * r ^ 2 at he
      linarith
    refine ⟨energyRadius r e, Real.sqrt_pos.mpr hp, ?_⟩
    unfold radialEnergy energyRadius
    rw [Real.sq_sqrt hp.le]
    ring

/-- The energy-side density includes the original s² Jacobian. Its continuity for continuous F is proved below. -/
def radialDensity (r : ℝ) (F : ℝ → ℝ) (e : ℝ) : ℝ :=
  energyRadius r e / 4 * F (energyRadius r e)

theorem radial_energy_change (r : ℝ) (F ρ : ℝ → ℝ) :
    (∫ s in Ioi 0, s ^ 2 * F s * ρ (radialEnergy r s)) =
      ∫ e in Iio (2 * r ^ 2), radialDensity r F e * ρ e := by
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s (_hs : s ∈ Ioi (0 : ℝ)) => (radialEnergy_derivative r s).hasDerivWithinAt)
    (radialEnergy_injective r) (fun e => radialDensity r F e * ρ e)
  rw [radialEnergy_image] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hp : 0 < s := hs
  simp only [radialDensity, energyRadius_of_energy r hp.le, smul_eq_mul]
  rw [abs_of_neg (by linarith : -4 * s < 0)]
  ring


theorem radialDensity_zero_above (r : ℝ) (F : ℝ → ℝ) {e : ℝ}
    (he : 2 * r ^ 2 ≤ e) : radialDensity r F e = 0 := by
  have ht : r ^ 2 - e / 2 ≤ 0 := by linarith
  simp [radialDensity, energyRadius, Real.sqrt_eq_zero_of_nonpos ht]

theorem radial_energy_change_global (r : ℝ) (F ρ : ℝ → ℝ) :
    (∫ s in Ioi 0, s ^ 2 * F s * ρ (radialEnergy r s)) =
      ∫ e, radialDensity r F e * ρ e := by
  rw [radial_energy_change]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro e he
  have hle : 2 * r ^ 2 ≤ e := le_of_not_gt he
  rw [radialDensity_zero_above r F hle, zero_mul]

theorem radialDensity_continuous (r : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (radialDensity r F) := by
  unfold radialDensity energyRadius
  fun_prop

theorem radialDensity_compactSupport (r : ℝ) (F : ℝ → ℝ) {M : ℝ} (hM : 0 < M)
    (hF : ∀ s, M < s → F s = 0) :
    HasCompactSupport (radialDensity r F) := by
  apply HasCompactSupport.intro (K := Icc (2 * r ^ 2 - 2 * M ^ 2) (2 * r ^ 2))
    isCompact_Icc
  intro e he
  rcases lt_or_ge e (2 * r ^ 2 - 2 * M ^ 2) with hlo | hlo
  · have hpos : 0 < r ^ 2 - e / 2 := by nlinarith
    have hs := Real.sq_sqrt hpos.le
    have hn := Real.sqrt_nonneg (r ^ 2 - e / 2)
    have hgt : M < energyRadius r e := by
      unfold energyRadius
      nlinarith
    rw [radialDensity, hF _ hgt, mul_zero]
  · have hhi : 2 * r ^ 2 < e := by
      by_contra h
      exact he ⟨hlo, le_of_not_gt h⟩
    exact radialDensity_zero_above r F hhi.le

theorem radialDensity_at_zero {r : ℝ} (hr : 0 ≤ r) (F : ℝ → ℝ) :
    radialDensity r F 0 = r / 4 * F r := by
  simp [radialDensity, energyRadius, Real.sqrt_sq hr]

/-- A genuine weak energy-layer limit of normalized kernels, including r=0.
The density being tested was obtained by the actual energy change of variables. -/
theorem radial_regularization_limit {r M : ℝ} (hr : 0 ≤ r) (hM : 0 < M)
    (F ρ : ℝ → ℝ) (hF : Continuous F) (hFtail : ∀ s, M < s → F s = 0)
    (hρ : ∀ e, 0 ≤ ρ e) (hρmass : ∫ e, ρ e = 1)
    (hρtail : Filter.Tendsto (fun e : ℝ => ‖e‖ * ρ e)
      (Bornology.cobounded ℝ) (nhds 0)) :
    Filter.Tendsto
      (fun c : ℝ => ∫ s in Ioi 0, s ^ 2 * F s * (c * ρ (c * radialEnergy r s)))
      Filter.atTop (nhds (r / 4 * F r)) := by
  have hgi : Integrable (radialDensity r F) :=
    (radialDensity_continuous r hF).integrable_of_hasCompactSupport
      (radialDensity_compactSupport r F hM hFtail)
  have hdecay : Filter.Tendsto (fun e : ℝ => ‖e‖ ^ Module.finrank ℝ ℝ * ρ e)
      (Bornology.cobounded ℝ) (nhds 0) := by simpa using hρtail
  have ht := tendsto_integral_comp_smul_smul_of_integrable hρ hρmass hdecay hgi
    (radialDensity_continuous r hF).continuousAt
  have heq (c : ℝ) :
      (∫ s in Ioi 0, s ^ 2 * F s * (c * ρ (c * radialEnergy r s))) =
        ∫ e : ℝ, (c ^ Module.finrank ℝ ℝ * ρ (c • e)) • radialDensity r F e := by
    rw [radial_energy_change_global r F (fun e => c * ρ (c * e))]
    apply integral_congr_ae
    filter_upwards [] with e
    simp [smul_eq_mul, mul_comm]
  simp_rw [heq]
  simpa only [radialDensity_at_zero hr F] using ht

/-- The zero-radius endpoint has zero limit with the original s² volume weight. -/
theorem zero_radius_regularization_limit {M : ℝ} (hM : 0 < M)
    (F ρ : ℝ → ℝ) (hF : Continuous F) (hFtail : ∀ s, M < s → F s = 0)
    (hρ : ∀ e, 0 ≤ ρ e) (hρmass : ∫ e, ρ e = 1)
    (hρtail : Filter.Tendsto (fun e : ℝ => ‖e‖ * ρ e)
      (Bornology.cobounded ℝ) (nhds 0)) :
    Filter.Tendsto
      (fun c : ℝ => ∫ s in Ioi 0, s ^ 2 * F s * (c * ρ (c * radialEnergy 0 s)))
      Filter.atTop (nhds 0) := by
  simpa using radial_regularization_limit (r := 0) (by norm_num) hM F ρ hF hFtail hρ hρmass hρtail

theorem regular_level_coefficient {r : ℝ} (hr : 0 < r) :
    (r / 4 : ℝ) = r ^ 2 * (1 / (4 * r)) := by
  field_simp

/-- Coefficient algebra for the proved Cartesian factor and radial density, with the first polar factor r². This does not itself identify the full measures. -/
theorem complete_pairing_coefficient (r : ℝ) :
    (8 : ℝ) * r ^ 2 * (r / 4) = 2 * r ^ 3 := by ring


/-- An explicit normalized energy-layer kernel. No Dirac measure is defined here. -/
def boxKernel : ℝ → ℝ := (Icc (-1) 1).indicator (fun _ => (1 / 2 : ℝ))

theorem boxKernel_nonneg (e : ℝ) : 0 ≤ boxKernel e := by
  by_cases he : e ∈ Icc (-1 : ℝ) 1 <;> simp [boxKernel, he]

theorem boxKernel_integral : (∫ e, boxKernel e) = 1 := by
  rw [boxKernel, integral_indicator_const _ measurableSet_Icc]
  norm_num [Measure.real, Real.volume_Icc]

theorem boxKernel_tail :
    Filter.Tendsto (fun e : ℝ => ‖e‖ * boxKernel e)
      (Bornology.cobounded ℝ) (nhds 0) := by
  have hc : HasCompactSupport (fun e : ℝ => ‖e‖ * boxKernel e) := by
    apply HasCompactSupport.intro (K := Icc (-1) 1) isCompact_Icc
    intro e he
    simp [boxKernel, he]
  have he := hasCompactSupport_iff_eventuallyEq.mp hc
  rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at he
  exact Filter.Tendsto.congr' he.symm tendsto_const_nhds

/-- Concrete normalized rectangular layers converge to the actual radial density,
including the critical endpoint r=0. -/
theorem box_radial_regularization_limit {r M : ℝ} (hr : 0 ≤ r) (hM : 0 < M)
    (F : ℝ → ℝ) (hF : Continuous F) (hFtail : ∀ s, M < s → F s = 0) :
    Filter.Tendsto
      (fun c : ℝ => ∫ s in Ioi 0, s ^ 2 * F s *
        (c * boxKernel (c * radialEnergy r s)))
      Filter.atTop (nhds (r / 4 * F r)) :=
  radial_regularization_limit hr hM F boxKernel hF hFtail
    boxKernel_nonneg boxKernel_integral boxKernel_tail

/-- The four original cube indicators are kept together in every readout. -/
def allFourFlags (R : ℝ) : Set FourMomenta :=
  {k | ∀ i, k i ∈ ResonantMeasure.cube R}

def sharpReadout (R : ℝ) (Φ : FourMomenta → ℝ) : FourMomenta → ℝ :=
  (allFourFlags R).indicator Φ

def energy (k : FourMomenta) : ℝ :=
  ‖k 0‖ ^ 2 + ‖k 1‖ ^ 2 - ‖k 2‖ ^ 2 - ‖k 3‖ ^ 2

theorem allFourFlags_measurable (R : ℝ) : MeasurableSet (allFourFlags R) := by
  simp only [allFourFlags, setOf_forall]
  exact MeasurableSet.iInter fun i =>
    (ResonantMeasure.measurable_cube R).preimage (measurable_pi_apply i)

theorem momentumAt_continuous (i : Fin 3) : Continuous (fun z : Nine => momentumAt z i) := by
  unfold momentumAt
  fun_prop

theorem physicalFour_continuous : Continuous physicalFour := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact momentumAt_continuous 0
  · exact momentumAt_continuous 1
  · exact momentumAt_continuous 2
  · exact ((momentumAt_continuous 0).add (momentumAt_continuous 1)).sub
      (momentumAt_continuous 2)

theorem sharpReadout_measurable (R : ℝ) {Φ : FourMomenta → ℝ}
    (hΦ : Measurable Φ) : Measurable (sharpReadout R Φ) :=
  hΦ.indicator (allFourFlags_measurable R)

theorem energy_continuous : Continuous energy := by
  unfold energy
  fun_prop

/-- Exact Cartesian change of variables for the same full sharp four-leg energy layer. -/
theorem cartesian_sharp_energy_layer (R c : ℝ) (Φ : FourMomenta → ℝ) (ρ : ℝ → ℝ)
    (hΦ : Measurable Φ) (hρ : Measurable ρ) :
    (∫ z : Nine, sharpReadout R Φ (physicalFour z) *
      (c * ρ (c * energy (physicalFour z)))) =
    8 * ∫ z : Nine, sharpReadout R Φ (pairedFour z) *
      (c * ρ (c * radialEnergy ‖momentumAt z 1‖ ‖momentumAt z 2‖)) := by
  have hm : Measurable (fun z : Nine => sharpReadout R Φ (physicalFour z) *
      (c * ρ (c * energy (physicalFour z)))) := by
    apply Measurable.mul
    · exact (sharpReadout_measurable R hΦ).comp physicalFour_continuous.measurable
    · exact measurable_const.mul
        (hρ.comp (measurable_const.mul
          (energy_continuous.measurable.comp physicalFour_continuous.measurable)))
  have ht := four_leg_integral_change
    (fun k => sharpReadout R Φ k * (c * ρ (c * energy k))) hm.aestronglyMeasurable
  have he (z : Nine) : energy (pairedFour z) =
      radialEnergy ‖momentumAt z 1‖ ‖momentumAt z 2‖ :=
    paired_energy_difference z
  simpa only [he] using ht


/-- Off-shell four-leg coordinates: the two pair radii have not yet been identified. -/
def radialFour (V : E) (r : ℝ) (σ : ResonantMeasure.Sphere)
    (s : ℝ) (τ : ResonantMeasure.Sphere) : FourMomenta :=
  ![V + r • (σ : E), V - r • (σ : E),
    V + s • (τ : E), V - s • (τ : E)]

theorem radialFour_continuous (V : E) (r : ℝ) (σ τ : ResonantMeasure.Sphere) :
    Continuous (fun s : ℝ => radialFour V r σ s τ) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const.add (continuous_id.smul continuous_const)
  · exact continuous_const.sub (continuous_id.smul continuous_const)

theorem radialFour_energy (V : E) (r s : ℝ) (σ τ : ResonantMeasure.Sphere) :
    energy (radialFour V r σ s τ) = radialEnergy r s := by
  have hp := parallelogram_law_with_norm ℝ V (r • (σ : E))
  have hq := parallelogram_law_with_norm ℝ V (s • (τ : E))
  have hrn : ‖r • (σ : E)‖ ^ 2 = r ^ 2 := by
    simp [norm_smul, Real.norm_eq_abs, sq_abs]
  have hsn : ‖s • (τ : E)‖ ^ 2 = s ^ 2 := by
    simp [norm_smul, Real.norm_eq_abs, sq_abs]
  change ‖V + r • (σ : E)‖ ^ 2 + ‖V - r • (σ : E)‖ ^ 2 -
    ‖V + s • (τ : E)‖ ^ 2 - ‖V - s • (τ : E)‖ ^ 2 =
      2 * (r ^ 2 - s ^ 2)
  rw [hrn] at hp
  rw [hsn] at hq
  linarith

theorem radialFour_on_level (p : ResonantMeasure.Parameters) :
    radialFour p.1 p.2.1 p.2.2.1 p.2.1 p.2.2.2 = ResonantMeasure.paired p := rfl

/-- The regular energy-layer limit reads the very same quartet in the frozen pairing map.
The hypothesis here is continuity of the test before any sharp indicator is inserted;
the Cartesian sharp-indicator identity above is separate. -/
theorem same_four_leg_radial_limit (p : ResonantMeasure.Parameters) {M : ℝ}
    (hM : 0 < M) (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hTail : ∀ s, M < s → Φ (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2) = 0) :
    Filter.Tendsto
      (fun c : ℝ => ∫ s in Ioi 0, s ^ 2 *
        Φ (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2) *
        (c * boxKernel (c * energy
          (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2))))
      Filter.atTop (nhds ((p.2.1 : ℝ) / 4 * Φ (ResonantMeasure.paired p))) := by
  have ht := box_radial_regularization_limit p.2.1.property.le hM
    (fun s => Φ (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2))
    (hΦ.comp (radialFour_continuous _ _ _ _)) hTail
  simpa only [radialFour_energy, radialFour_on_level] using ht


/-- The coordinate map from the exact thermodynamic momentum carrier to the
Euclidean carrier used by the common resonance measure. -/
def toMomentumE : Thermodynamics.Momentum → E := WithLp.toLp 2

theorem toMomentumE_volume_preserving :
    MeasurePreserving toMomentumE (volume : Measure Thermodynamics.Momentum)
      (volume : Measure E) :=
  PiLp.volume_preserving_toLp (Fin 3)

theorem toMomentumE_map_volume :
    Measure.map toMomentumE (volume : Measure Thermodynamics.Momentum) =
      (volume : Measure E) :=
  toMomentumE_volume_preserving.map_eq

theorem toMomentumE_cube_preimage (R : ℝ) :
    toMomentumE ⁻¹' ResonantMeasure.cube R = Entropy.sharpCube R := by
  ext k
  change (∀ j : Fin 3, |k j| ≤ R) ↔
    ((fun _ : Fin 3 => -R) ≤ k ∧ k ≤ (fun _ : Fin 3 => R))
  constructor
  · intro h
    exact ⟨fun j => (abs_le.mp (h j)).1, fun j => (abs_le.mp (h j)).2⟩
  · rintro ⟨hl, hu⟩ j
    exact abs_le.mpr ⟨hl j, hu j⟩

theorem toMomentumE_cube_preserving (R : ℝ) :
    MeasurePreserving toMomentumE (Entropy.cubeMeasure R)
      ((volume : Measure E).restrict (ResonantMeasure.cube R)) := by
  have h := toMomentumE_volume_preserving.restrict_preimage
    (ResonantMeasure.measurable_cube R)
  simpa only [toMomentumE_cube_preimage, Entropy.cubeMeasure] using h

theorem toMomentumE_map_cube (R : ℝ) :
    Measure.map toMomentumE (Entropy.cubeMeasure R) =
      (volume : Measure E).restrict (ResonantMeasure.cube R) :=
  (toMomentumE_cube_preserving R).map_eq

/-- The thermodynamic and Euclidean sharp-cube integrals are exactly the same;
there is no extra geometric normalization. -/
theorem thermodynamic_cube_integral (R : ℝ) (F : E → ℝ)
    (hF : AEStronglyMeasurable F
      ((volume : Measure E).restrict (ResonantMeasure.cube R))) :
    (∫ k, F k ∂(volume : Measure E).restrict (ResonantMeasure.cube R)) =
      ∫ p, F (toMomentumE p) ∂Entropy.cubeMeasure R := by
  have hfmap : AEStronglyMeasurable F
      (Measure.map toMomentumE (Entropy.cubeMeasure R)) := by
    rw [toMomentumE_map_cube]
    exact hF
  have ht := integral_map (toMomentumE_cube_preserving R).measurable.aemeasurable hfmap
  simpa only [toMomentumE_map_cube] using ht

def euclideanFive (i : Fin 5) (k : E) : ℝ :=
  ![1, k 0, k 1, k 2, ‖k‖ ^ 2] i

theorem euclideanFive_coordinate (i : Fin 5) (p : Thermodynamics.Momentum) :
    euclideanFive i (toMomentumE p) = Entropy.fiveInvariants i p := by
  have hn : ‖toMomentumE p‖ ^ 2 = ∑ j : Fin 3, (p j) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [toMomentumE, Real.norm_eq_abs, sq_abs]
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hn

theorem euclidean_denominator_coordinate (θ : Thermodynamics.Parameter)
    (p : Thermodynamics.Momentum) :
    Entropy.denominator euclideanFive θ (toMomentumE p) =
      Entropy.denominator Entropy.fiveInvariants θ p := by
  unfold Entropy.denominator
  apply Finset.sum_congr rfl
  intro i _
  rw [euclideanFive_coordinate]


theorem euclideanFive_continuous (i : Fin 5) : Continuous (euclideanFive i) := by
  change Continuous (fun k : E => ![1, k 0, k 1, k 2, ‖k‖ ^ 2] i)
  fin_cases i <;> dsimp <;> fun_prop

theorem euclidean_rj_coordinate (θ : Thermodynamics.Parameter)
    (p : Thermodynamics.Momentum) :
    Entropy.rj euclideanFive θ (toMomentumE p) =
      Entropy.rj Entropy.fiveInvariants θ p := by
  simp only [Entropy.rj, euclidean_denominator_coordinate]

theorem thermodynamic_momentMap_euclidean (R : ℝ) (θ : Thermodynamics.Parameter)
    (i : Fin 5) :
    Thermodynamics.momentMap R θ i =
      ∫ k in ResonantMeasure.cube R, euclideanFive i k * Entropy.rj euclideanFive θ k := by
  have hd : Continuous (Entropy.denominator euclideanFive θ) := by
    unfold Entropy.denominator
    exact continuous_finset_sum Finset.univ
      (fun j _ => continuous_const.mul (euclideanFive_continuous j))
  have hm : Measurable (fun k : E => euclideanFive i k * Entropy.rj euclideanFive θ k) :=
    (euclideanFive_continuous i).measurable.mul hd.measurable.inv
  have ht := thermodynamic_cube_integral R
    (fun k => euclideanFive i k * Entropy.rj euclideanFive θ k)
    hm.aestronglyMeasurable
  symm
  simpa only [euclideanFive_coordinate, euclidean_rj_coordinate,
    Thermodynamics.momentMap, Entropy.moment] using ht

/-! Explicit type and kernel-axiom audit of every theorem in this module. -/
#check blockMatrix_det
#check coordinateMatrix_det
#check coordinateMap_zero
#check coordinateMap_one
#check coordinateMap_two
#check coordinateMap_measurable
#check coordinateMap_volume
#check cartesian_integral_change
#check coordinate_four_identity
#check four_leg_integral_change
#check paired_energy_difference
#check radialEnergy_derivative
#check radialEnergy_injective
#check energyRadius_of_energy
#check radialEnergy_image
#check radial_energy_change
#check radialDensity_zero_above
#check radial_energy_change_global
#check radialDensity_continuous
#check radialDensity_compactSupport
#check radialDensity_at_zero
#check radial_regularization_limit
#check zero_radius_regularization_limit
#check regular_level_coefficient
#check complete_pairing_coefficient
#check boxKernel_nonneg
#check boxKernel_integral
#check boxKernel_tail
#check box_radial_regularization_limit
#check allFourFlags_measurable
#check momentumAt_continuous
#check physicalFour_continuous
#check sharpReadout_measurable
#check energy_continuous
#check cartesian_sharp_energy_layer
#check radialFour_continuous
#check radialFour_energy
#check radialFour_on_level
#check same_four_leg_radial_limit
#check toMomentumE_volume_preserving
#check toMomentumE_map_volume
#check toMomentumE_cube_preimage
#check toMomentumE_cube_preserving
#check toMomentumE_map_cube
#check thermodynamic_cube_integral
#check euclideanFive_coordinate
#check euclidean_denominator_coordinate
#check euclideanFive_continuous
#check euclidean_rj_coordinate
#check thermodynamic_momentMap_euclidean
#print axioms blockMatrix_det
#print axioms coordinateMatrix_det
#print axioms coordinateMap_zero
#print axioms coordinateMap_one
#print axioms coordinateMap_two
#print axioms coordinateMap_measurable
#print axioms coordinateMap_volume
#print axioms cartesian_integral_change
#print axioms coordinate_four_identity
#print axioms four_leg_integral_change
#print axioms paired_energy_difference
#print axioms radialEnergy_derivative
#print axioms radialEnergy_injective
#print axioms energyRadius_of_energy
#print axioms radialEnergy_image
#print axioms radial_energy_change
#print axioms radialDensity_zero_above
#print axioms radial_energy_change_global
#print axioms radialDensity_continuous
#print axioms radialDensity_compactSupport
#print axioms radialDensity_at_zero
#print axioms radial_regularization_limit
#print axioms zero_radius_regularization_limit
#print axioms regular_level_coefficient
#print axioms complete_pairing_coefficient
#print axioms boxKernel_nonneg
#print axioms boxKernel_integral
#print axioms boxKernel_tail
#print axioms box_radial_regularization_limit
#print axioms allFourFlags_measurable
#print axioms momentumAt_continuous
#print axioms physicalFour_continuous
#print axioms sharpReadout_measurable
#print axioms energy_continuous
#print axioms cartesian_sharp_energy_layer
#print axioms radialFour_continuous
#print axioms radialFour_energy
#print axioms radialFour_on_level
#print axioms same_four_leg_radial_limit
#print axioms toMomentumE_volume_preserving
#print axioms toMomentumE_map_volume
#print axioms toMomentumE_cube_preimage
#print axioms toMomentumE_cube_preserving
#print axioms toMomentumE_map_cube
#print axioms thermodynamic_cube_integral
#print axioms euclideanFive_coordinate
#print axioms euclidean_denominator_coordinate
#print axioms euclideanFive_continuous
#print axioms euclidean_rj_coordinate
#print axioms thermodynamic_momentMap_euclidean

end
end Resonance.CoareaNormalization
