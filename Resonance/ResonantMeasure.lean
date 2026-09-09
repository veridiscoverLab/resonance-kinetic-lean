import Mathlib
import Resonance.Collision

/-!
A concrete common four-leg measure from global pair coordinates.
The angular measure is Mathlib's Haar-induced Euclidean sphere measure,
with its existing polar-coordinate theorem.  The identification with the
manuscript's momentum/energy coarea measure is a separate theorem, not an
assumption or a field in the definitions below.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise

namespace Resonance.ResonantMeasure
noncomputable section

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : E) 1
abbrev Radius := Set.Ioi (0 : ℝ)
abbrev Parameters := E × (Radius × (Sphere × Sphere))
abbrev FourMomenta := Fin 4 → E

def surface : Measure Sphere := (volume : Measure E).toSphere
def radial : Measure Radius := Measure.volumeIoiPow 3
def base : Measure Parameters := (volume : Measure E).prod (radial.prod (surface.prod surface))

instance : IsFiniteMeasure surface := by unfold surface; infer_instance
instance : SigmaFinite radial := by unfold radial; infer_instance
instance : SigmaFinite base := by unfold base; infer_instance

def paired (p : Parameters) : FourMomenta :=
  ![p.1 + (p.2.1 : ℝ) • (p.2.2.1 : E),
    p.1 - (p.2.1 : ℝ) • (p.2.2.1 : E),
    p.1 + (p.2.1 : ℝ) • (p.2.2.2 : E),
    p.1 - (p.2.1 : ℝ) • (p.2.2.2 : E)]

def cube (R : ℝ) : Set E := {k | ∀ j : Fin 3, |k j| ≤ R}
def allowed (R : ℝ) : Set Parameters := {p | ∀ i : Fin 4, paired p i ∈ cube R}

/-- The radius density is exactly 2r³, with all four original sharp flags. -/
def parameterMeasure (R : ℝ) : Measure Parameters := (2 : ℝ≥0∞) • base.restrict (allowed R)
def pairingMeasure (R : ℝ) : Measure FourMomenta := Measure.map paired (parameterMeasure R)

theorem continuous_paired : Continuous paired := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [paired] <;> fun_prop

theorem measurable_cube (R : ℝ) : MeasurableSet (cube R) := by
  have hc : IsClosed (cube R) := by
    change IsClosed {k : E | ∀ j : Fin 3, |k j| ≤ R}
    simp only [setOf_forall]
    apply isClosed_iInter
    intro j
    exact isClosed_le (by fun_prop) continuous_const
  exact hc.measurableSet

theorem measurable_allowed (R : ℝ) : MeasurableSet (allowed R) := by
  change MeasurableSet {p : Parameters | ∀ i : Fin 4, paired p i ∈ cube R}
  simp only [setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_cube R).preimage
    ((continuous_apply i).comp continuous_paired).measurable)

theorem sphere_norm (s : Sphere) : ‖(s : E)‖ = 1 := by
  simp

theorem paired_momentum (p : Parameters) :
    paired p 0 + paired p 1 = paired p 2 + paired p 3 := by
  simp [paired]

theorem paired_energy (p : Parameters) :
    ‖paired p 0‖ ^ 2 + ‖paired p 1‖ ^ 2 =
      ‖paired p 2‖ ^ 2 + ‖paired p 3‖ ^ 2 := by
  change ‖p.1 + (p.2.1 : ℝ) • (p.2.2.1 : E)‖ ^ 2 +
    ‖p.1 - (p.2.1 : ℝ) • (p.2.2.1 : E)‖ ^ 2 =
    ‖p.1 + (p.2.1 : ℝ) • (p.2.2.2 : E)‖ ^ 2 +
    ‖p.1 - (p.2.1 : ℝ) • (p.2.2.2 : E)‖ ^ 2
  rw [parallelogram_law_with_norm ℝ, parallelogram_law_with_norm ℝ]
  simp [norm_smul]

theorem norm_le_three_R {R : ℝ} (hR : 0 ≤ R) {k : E} (hk : k ∈ cube R) :
    ‖k‖ ≤ 3 * R := by
  have hs (j : Fin 3) : (k j) ^ 2 ≤ R ^ 2 := by
    have hj := (abs_le.mp (hk j))
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
  rw [← EuclideanSpace.real_norm_sq_eq] at hsum
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  nlinarith [norm_nonneg k]

theorem parameter_bounds {R : ℝ} (hR : 0 ≤ R) {p : Parameters} (hp : p ∈ allowed R) :
    ‖p.1‖ ≤ 3 * R ∧ (p.2.1 : ℝ) ≤ 3 * R := by
  have h0 := norm_le_three_R hR (hp 0)
  have h1 := norm_le_three_R hR (hp 1)
  have ha := norm_add_le (paired p 0) (paired p 1)
  have hs := norm_sub_le (paired p 0) (paired p 1)
  have eadd : paired p 0 + paired p 1 = (2 : ℝ) • p.1 := by
    simp [paired, two_smul]
  have esub : paired p 0 - paired p 1 =
      (2 * (p.2.1 : ℝ)) • (p.2.2.1 : E) := by
    simp [paired, sub_eq_add_neg, add_smul, two_mul, add_left_comm, add_assoc]
  rw [eadd, norm_smul] at ha
  rw [esub, norm_smul, sphere_norm] at hs
  have hr : 0 < (p.2.1 : ℝ) := p.2.1.property
  simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at hs
  constructor <;> nlinarith

def antipode (s : Sphere) : Sphere :=
  ⟨-(s : E), by simp⟩

theorem continuous_antipode : Continuous antipode := by
  apply Continuous.subtype_mk
  fun_prop

theorem antipode_involutive : Function.Involutive antipode := by
  intro s
  apply Subtype.ext
  simp [antipode]

theorem cone_antipode (s : Set Sphere) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (antipode ⁻¹' s)) =
      Neg.neg ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨a, ha, rfl⟩, hxy⟩
    refine ⟨r, hr, -(a : E), ⟨antipode a, ha, rfl⟩, ?_⟩
    simpa [smul_neg] using congrArg Neg.neg hxy
  · rintro ⟨r, hr, y, ⟨a, ha, rfl⟩, hxy⟩
    refine ⟨r, hr, -(a : E), ⟨antipode a, ?_, rfl⟩, ?_⟩
    · simpa [antipode_involutive a] using ha
    · simpa [smul_neg] using congrArg Neg.neg hxy

theorem antipode_preserves_surface :
    MeasurePreserving antipode surface surface := by
  refine ⟨continuous_antipode.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply continuous_antipode.measurable hs]
  change (volume : Measure E).toSphere (antipode ⁻¹' s) = (volume : Measure E).toSphere s
  rw [Measure.toSphere_apply' _ (continuous_antipode.measurable hs),
      Measure.toSphere_apply' _ hs, cone_antipode, Measure.measure_preimage_neg]


theorem base_allowed_finite {R : ℝ} (hR : 0 ≤ R) : base (allowed R) < ∞ := by
  let upper : Radius := ⟨3 * R + 1, by show 0 < 3 * R + 1; linarith⟩
  have hb : allowed R ⊆
      closedBall (0 : E) (3 * R) ×ˢ (Iio upper ×ˢ (univ : Set (Sphere × Sphere))) := by
    intro p hp
    have h := parameter_bounds hR hp
    refine ⟨?_, ?_, trivial⟩
    · simpa [mem_closedBall, dist_zero_right] using h.1
    · change (p.2.1 : ℝ) < 3 * R + 1
      linarith [h.2]
  apply lt_of_le_of_lt (measure_mono hb)
  rw [base, Measure.prod_prod, Measure.prod_prod]
  have hV : (volume : Measure E) (closedBall 0 (3 * R)) < ∞ :=
    (isCompact_closedBall (0 : E) (3 * R)).measure_lt_top
  have hr : radial (Iio upper) < ∞ := by
    rw [radial, Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top
  have hs : (surface.prod surface) univ < ∞ := measure_lt_top _ _
  exact ENNReal.mul_lt_top hV (ENNReal.mul_lt_top hr hs)

theorem parameterMeasure_finite {R : ℝ} (hR : 0 ≤ R) :
    IsFiniteMeasure (parameterMeasure R) := by
  constructor
  simp only [parameterMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top (by norm_num) (base_allowed_finite hR)

theorem pairingMeasure_finite {R : ℝ} (hR : 0 ≤ R) :
    IsFiniteMeasure (pairingMeasure R) := by
  letI := parameterMeasure_finite hR
  unfold pairingMeasure
  infer_instance

def swapIncomingP : Parameters → Parameters :=
  Prod.map id (Prod.map id (Prod.map antipode id))
def swapOutgoingP : Parameters → Parameters :=
  Prod.map id (Prod.map id (Prod.map id antipode))
def swapPairsP : Parameters → Parameters :=
  Prod.map id (Prod.map id Prod.swap)

def swapIncomingK (k : FourMomenta) : FourMomenta := ![k 1, k 0, k 2, k 3]
def swapOutgoingK (k : FourMomenta) : FourMomenta := ![k 0, k 1, k 3, k 2]
def swapPairsK (k : FourMomenta) : FourMomenta := ![k 2, k 3, k 0, k 1]

theorem incoming_preserves_base : MeasurePreserving swapIncomingP base base :=
  (MeasurePreserving.id volume).prod
    ((MeasurePreserving.id radial).prod
      (antipode_preserves_surface.prod (MeasurePreserving.id surface)))

theorem outgoing_preserves_base : MeasurePreserving swapOutgoingP base base :=
  (MeasurePreserving.id volume).prod
    ((MeasurePreserving.id radial).prod
      ((MeasurePreserving.id surface).prod antipode_preserves_surface))

theorem pairs_preserves_base : MeasurePreserving swapPairsP base base :=
  (MeasurePreserving.id volume).prod
    ((MeasurePreserving.id radial).prod Measure.measurePreserving_swap)

theorem paired_swapIncoming (p : Parameters) :
    paired (swapIncomingP p) = swapIncomingK (paired p) := by
  funext i
  fin_cases i <;> simp [paired, swapIncomingP, swapIncomingK, antipode, sub_eq_add_neg]

theorem paired_swapOutgoing (p : Parameters) :
    paired (swapOutgoingP p) = swapOutgoingK (paired p) := by
  funext i
  fin_cases i <;> simp [paired, swapOutgoingP, swapOutgoingK, antipode, sub_eq_add_neg]

theorem paired_swapPairs (p : Parameters) :
    paired (swapPairsP p) = swapPairsK (paired p) := by
  funext i
  fin_cases i <;> simp [paired, swapPairsP, swapPairsK]

theorem incoming_allowed (R : ℝ) : swapIncomingP ⁻¹' allowed R = allowed R := by
  ext p
  change (∀ i, paired (swapIncomingP p) i ∈ cube R) ↔ (∀ i, paired p i ∈ cube R)
  rw [paired_swapIncoming]
  simp only [swapIncomingK, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  tauto

theorem outgoing_allowed (R : ℝ) : swapOutgoingP ⁻¹' allowed R = allowed R := by
  ext p
  change (∀ i, paired (swapOutgoingP p) i ∈ cube R) ↔ (∀ i, paired p i ∈ cube R)
  rw [paired_swapOutgoing]
  simp only [swapOutgoingK, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  tauto

theorem pairs_allowed (R : ℝ) : swapPairsP ⁻¹' allowed R = allowed R := by
  ext p
  change (∀ i, paired (swapPairsP p) i ∈ cube R) ↔ (∀ i, paired p i ∈ cube R)
  rw [paired_swapPairs]
  simp only [swapPairsK, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  tauto


theorem incoming_preserves_parameters (R : ℝ) :
    MeasurePreserving swapIncomingP (parameterMeasure R) (parameterMeasure R) := by
  have h := incoming_preserves_base.restrict_preimage (measurable_allowed R)
  rw [incoming_allowed] at h
  exact h.smul_measure (2 : ℝ≥0∞)

theorem outgoing_preserves_parameters (R : ℝ) :
    MeasurePreserving swapOutgoingP (parameterMeasure R) (parameterMeasure R) := by
  have h := outgoing_preserves_base.restrict_preimage (measurable_allowed R)
  rw [outgoing_allowed] at h
  exact h.smul_measure (2 : ℝ≥0∞)

theorem pairs_preserves_parameters (R : ℝ) :
    MeasurePreserving swapPairsP (parameterMeasure R) (parameterMeasure R) := by
  have h := pairs_preserves_base.restrict_preimage (measurable_allowed R)
  rw [pairs_allowed] at h
  exact h.smul_measure (2 : ℝ≥0∞)

theorem map_paired_symmetry (R : ℝ) (T : Parameters → Parameters)
    (S : FourMomenta → FourMomenta)
    (hT : MeasurePreserving T (parameterMeasure R) (parameterMeasure R))
    (hS : Measurable S) (hcomm : ∀ p, paired (T p) = S (paired p)) :
    MeasurePreserving S (pairingMeasure R) (pairingMeasure R) := by
  refine ⟨hS, ?_⟩
  unfold pairingMeasure
  rw [Measure.map_map hS continuous_paired.measurable]
  have he : S ∘ paired = paired ∘ T := funext (fun p => (hcomm p).symm)
  rw [he, ← Measure.map_map continuous_paired.measurable hT.measurable, hT.map_eq]

theorem incoming_preserves_pairing (R : ℝ) :
    MeasurePreserving swapIncomingK (pairingMeasure R) (pairingMeasure R) := by
  apply map_paired_symmetry R swapIncomingP swapIncomingK (incoming_preserves_parameters R)
  · apply Continuous.measurable
    apply continuous_pi
    intro i
    fin_cases i <;> exact continuous_apply _
  · exact paired_swapIncoming

theorem outgoing_preserves_pairing (R : ℝ) :
    MeasurePreserving swapOutgoingK (pairingMeasure R) (pairingMeasure R) := by
  apply map_paired_symmetry R swapOutgoingP swapOutgoingK (outgoing_preserves_parameters R)
  · apply Continuous.measurable
    apply continuous_pi
    intro i
    fin_cases i <;> exact continuous_apply _
  · exact paired_swapOutgoing

theorem pairs_preserves_pairing (R : ℝ) :
    MeasurePreserving swapPairsK (pairingMeasure R) (pairingMeasure R) := by
  apply map_paired_symmetry R swapPairsP swapPairsK (pairs_preserves_parameters R)
  · apply Continuous.measurable
    apply continuous_pi
    intro i
    fin_cases i <;> exact continuous_apply _
  · exact paired_swapPairs

def fullResonance (R : ℝ) : Set FourMomenta :=
  {k | (∀ i : Fin 4, k i ∈ cube R) ∧
    k 0 + k 1 = k 2 + k 3 ∧
    ‖k 0‖ ^ 2 + ‖k 1‖ ^ 2 = ‖k 2‖ ^ 2 + ‖k 3‖ ^ 2}

theorem measurable_fullResonance (R : ℝ) : MeasurableSet (fullResonance R) := by
  have hflags : MeasurableSet {k : FourMomenta | ∀ i : Fin 4, k i ∈ cube R} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun i => (measurable_cube R).preimage (measurable_pi_apply i))
  exact hflags.inter ((measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)))

theorem pairing_supported_on_fullResonance (R : ℝ) :
    pairingMeasure R (fullResonance R)ᶜ = 0 := by
  rw [pairingMeasure, Measure.map_apply continuous_paired.measurable
    (measurable_fullResonance R).compl]
  rw [parameterMeasure, Measure.smul_apply, Measure.restrict_apply
    (continuous_paired.measurable (measurable_fullResonance R).compl)]
  have he : (paired ⁻¹' (fullResonance R)ᶜ) ∩ allowed R = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hp.1 ⟨hp.2, paired_momentum p, paired_energy p⟩
  rw [he]
  simp

/-- Every leg is a translation of the same center V, with the other variables fixed. -/
def legShift (i : Fin 4) (b : Radius × (Sphere × Sphere)) : E :=
  ![(b.1 : ℝ) • (b.2.1 : E), -(b.1 : ℝ) • (b.2.1 : E),
    (b.1 : ℝ) • (b.2.2 : E), -(b.1 : ℝ) • (b.2.2 : E)] i

theorem paired_leg_translate (p : Parameters) (i : Fin 4) :
    paired p i = p.1 + legShift i p.2 := by
  fin_cases i <;> simp [paired, legShift, sub_eq_add_neg]

theorem measurable_legShift (i : Fin 4) : Measurable (legShift i) := by
  fin_cases i
  · change Measurable (fun b : Radius × (Sphere × Sphere) => (b.1 : ℝ) • (b.2.1 : E))
    fun_prop
  · change Measurable (fun b : Radius × (Sphere × Sphere) => -(b.1 : ℝ) • (b.2.1 : E))
    fun_prop
  · change Measurable (fun b : Radius × (Sphere × Sphere) => (b.1 : ℝ) • (b.2.2 : E))
    fun_prop
  · change Measurable (fun b : Radius × (Sphere × Sphere) => -(b.1 : ℝ) • (b.2.2 : E))
    fun_prop

theorem base_single_leg_null (i : Fin 4) {s : Set E} (hs : MeasurableSet s)
    (hzero : (volume : Measure E) s = 0) :
    base ((fun p => paired p i) ⁻¹' s) = 0 := by
  have hset : MeasurableSet ((fun p : Parameters => paired p i) ⁻¹' s) :=
    hs.preimage ((measurable_pi_apply i).comp continuous_paired.measurable)
  rw [base, Measure.prod_apply_symm hset]
  have hsection (b : Radius × (Sphere × Sphere)) :
      (volume : Measure E) ((fun V : E => (V, b)) ⁻¹' ((fun p => paired p i) ⁻¹' s)) = 0 := by
    have he : ((fun V : E => (V, b)) ⁻¹' ((fun p => paired p i) ⁻¹' s)) =
        (fun V : E => V + legShift i b) ⁻¹' s := by
      ext V
      simp only [mem_preimage, paired_leg_translate]
    rw [he]
    simpa only [id_eq] using (((MeasurePreserving.id (volume : Measure E)).add_right
      (volume : Measure E) (legShift i b)).measure_preimage hs.nullMeasurableSet).trans hzero
  simp_rw [hsection]
  simp

theorem pairing_single_leg_null (R : ℝ) (i : Fin 4) {s : Set E}
    (hs : MeasurableSet s) (hzero : (volume : Measure E) s = 0) :
    pairingMeasure R ((fun k => k i) ⁻¹' s) = 0 := by
  rw [pairingMeasure, Measure.map_apply continuous_paired.measurable
    (hs.preimage (measurable_pi_apply i))]
  change parameterMeasure R ((fun p => paired p i) ⁻¹' s) = 0
  have hb := base_single_leg_null i hs hzero
  have hr : (base.restrict (allowed R)) ((fun p => paired p i) ⁻¹' s) = 0 :=
    le_antisymm (le_trans (Measure.restrict_le_self _) hb.le) (zero_le _)
  simp only [parameterMeasure, Measure.smul_apply, hr, smul_zero]


theorem pairing_marginal_absolutelyContinuous (R : ℝ) (i : Fin 4) :
    Measure.map (fun k : FourMomenta => k i) (pairingMeasure R) ≪ (volume : Measure E) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  exact pairing_single_leg_null R i hs hzero

theorem marginal_via_symmetry (R : ℝ) (S : FourMomenta → FourMomenta)
    (hS : MeasurePreserving S (pairingMeasure R) (pairingMeasure R))
    (i j : Fin 4) (hij : ∀ k, S k i = k j) :
    Measure.map (fun k : FourMomenta => k j) (pairingMeasure R) =
      Measure.map (fun k : FourMomenta => k i) (pairingMeasure R) := by
  have he : (fun k : FourMomenta => k j) = (fun k => k i) ∘ S :=
    funext (fun k => (hij k).symm)
  rw [he, ← Measure.map_map (measurable_pi_apply i) hS.measurable, hS.map_eq]

/-- All four legs have exactly the same marginal of this one common measure. -/
theorem pairing_marginal_eq_zero (R : ℝ) (i : Fin 4) :
    Measure.map (fun k : FourMomenta => k i) (pairingMeasure R) =
      Measure.map (fun k : FourMomenta => k 0) (pairingMeasure R) := by
  fin_cases i
  · rfl
  · exact marginal_via_symmetry R swapIncomingK (incoming_preserves_pairing R)
      0 1 (fun k => rfl)
  · exact marginal_via_symmetry R swapPairsK (pairs_preserves_pairing R)
      0 2 (fun k => rfl)
  · exact (marginal_via_symmetry R swapPairsK (pairs_preserves_pairing R)
      1 3 (fun k => rfl)).trans
      (marginal_via_symmetry R swapIncomingK (incoming_preserves_pairing R)
      0 1 (fun k => rfl))

/-- The angular measure used above has the actual Euclidean polar Jacobian r². -/
theorem euclidean_polar_coordinates :
    MeasurePreserving (homeomorphUnitSphereProd E)
      ((volume : Measure E).comap Subtype.val)
      (surface.prod (Measure.volumeIoiPow 2)) := by
  simpa [surface, E] using
    (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E))


theorem base_allowed_positive {R : ℝ} (hR : 0 < R) : 0 < base (allowed R) := by
  let upper : Radius := ⟨R / 4, by show 0 < R / 4; positivity⟩
  let small : Set Parameters :=
    ball (0 : E) (R / 4) ×ˢ (Iio upper ×ˢ (univ : Set (Sphere × Sphere)))
  have hsmall : small ⊆ allowed R := by
    intro p hp i j
    have hV : ‖p.1‖ < R / 4 := by
      simpa [small, mem_ball, dist_zero_right] using hp.1
    have hr : (p.2.1 : ℝ) < R / 4 := hp.2.1
    have hrpos : 0 < (p.2.1 : ℝ) := p.2.1.property
    have hshift : ‖legShift i p.2‖ = (p.2.1 : ℝ) := by
      fin_cases i <;> simp [legShift, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
    have hk : ‖paired p i‖ ≤ ‖p.1‖ + (p.2.1 : ℝ) := by
      rw [paired_leg_translate]
      simpa [hshift] using norm_add_le p.1 (legShift i p.2)
    have hj : |paired p i j| ≤ ‖paired p i‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (paired p i) j
    exact hj.trans (by linarith)
  have hV : (volume : Measure E) (ball 0 (R / 4)) ≠ 0 :=
    isOpen_ball.measure_ne_zero _ (Metric.nonempty_ball.mpr (by positivity))
  have hr : radial (Iio upper) ≠ 0 := by
    rw [radial, Measure.volumeIoiPow_apply_Iio]
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    dsimp [upper]
    positivity
  have hsurf : surface univ ≠ 0 := by
    change (volume : Measure E).toSphere univ ≠ 0
    exact Measure.measure_univ_ne_zero.mpr
      (Measure.toSphere_ne_zero (volume : Measure E))
  have hbox : base small ≠ 0 := by
    dsimp [base, small]
    rw [Measure.prod_prod, Measure.prod_prod]
    have hs : (surface.prod surface) univ ≠ 0 := by
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      exact mul_ne_zero hsurf hsurf
    exact mul_ne_zero hV (mul_ne_zero hr hs)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hbox) (measure_mono hsmall)

theorem pairingMeasure_positive {R : ℝ} (hR : 0 < R) :
    0 < pairingMeasure R univ := by
  rw [pairingMeasure, Measure.map_apply continuous_paired.measurable MeasurableSet.univ]
  simp only [preimage_univ, parameterMeasure, Measure.smul_apply,
    Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_pos (by norm_num) (ne_of_gt (base_allowed_positive hR))




/-! Full theorem-type and transitive axiom audit. -/
#check continuous_paired
#check measurable_cube
#check measurable_allowed
#check sphere_norm
#check paired_momentum
#check paired_energy
#check norm_le_three_R
#check parameter_bounds
#check continuous_antipode
#check antipode_involutive
#check cone_antipode
#check antipode_preserves_surface
#check base_allowed_finite
#check parameterMeasure_finite
#check pairingMeasure_finite
#check incoming_preserves_base
#check outgoing_preserves_base
#check pairs_preserves_base
#check paired_swapIncoming
#check paired_swapOutgoing
#check paired_swapPairs
#check incoming_allowed
#check outgoing_allowed
#check pairs_allowed
#check incoming_preserves_parameters
#check outgoing_preserves_parameters
#check pairs_preserves_parameters
#check map_paired_symmetry
#check incoming_preserves_pairing
#check outgoing_preserves_pairing
#check pairs_preserves_pairing
#check measurable_fullResonance
#check pairing_supported_on_fullResonance
#check paired_leg_translate
#check measurable_legShift
#check base_single_leg_null
#check pairing_single_leg_null
#check pairing_marginal_absolutelyContinuous
#check marginal_via_symmetry
#check pairing_marginal_eq_zero
#check euclidean_polar_coordinates
#check base_allowed_positive
#check pairingMeasure_positive

#print axioms continuous_paired
#print axioms measurable_cube
#print axioms measurable_allowed
#print axioms sphere_norm
#print axioms paired_momentum
#print axioms paired_energy
#print axioms norm_le_three_R
#print axioms parameter_bounds
#print axioms continuous_antipode
#print axioms antipode_involutive
#print axioms cone_antipode
#print axioms antipode_preserves_surface
#print axioms base_allowed_finite
#print axioms parameterMeasure_finite
#print axioms pairingMeasure_finite
#print axioms incoming_preserves_base
#print axioms outgoing_preserves_base
#print axioms pairs_preserves_base
#print axioms paired_swapIncoming
#print axioms paired_swapOutgoing
#print axioms paired_swapPairs
#print axioms incoming_allowed
#print axioms outgoing_allowed
#print axioms pairs_allowed
#print axioms incoming_preserves_parameters
#print axioms outgoing_preserves_parameters
#print axioms pairs_preserves_parameters
#print axioms map_paired_symmetry
#print axioms incoming_preserves_pairing
#print axioms outgoing_preserves_pairing
#print axioms pairs_preserves_pairing
#print axioms measurable_fullResonance
#print axioms pairing_supported_on_fullResonance
#print axioms paired_leg_translate
#print axioms measurable_legShift
#print axioms base_single_leg_null
#print axioms pairing_single_leg_null
#print axioms pairing_marginal_absolutelyContinuous
#print axioms marginal_via_symmetry
#print axioms pairing_marginal_eq_zero
#print axioms euclidean_polar_coordinates
#print axioms base_allowed_positive
#print axioms pairingMeasure_positive

end
end Resonance.ResonantMeasure
