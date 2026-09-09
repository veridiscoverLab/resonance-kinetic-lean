import Resonance.CoareaGlobal
import Resonance.RectangularCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Volume.Measure

open MeasureTheory Set Metric
open scoped ENNReal NNReal EuclideanGeometry
namespace Resonance.PlaneCoarea
noncomputable section
set_option maxHeartbeats 600000
abbrev E := ResonantMeasure.E
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev Sphere := ResonantMeasure.Sphere
abbrev Radius := ResonantMeasure.Radius
abbrev FourMomenta := ResonantMeasure.FourMomenta

@[simp] theorem real_inner_apply (x y : ℝ) : inner ℝ x y = y * x := rfl

def e0 : E := EuclideanSpace.single 0 1

@[simp] theorem e0_norm : ‖e0‖ = 1 := by simp [e0]

def householder (σ : Sphere) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ (e0 - (σ : E)))ᗮ.reflection

theorem householder_e0 (σ : Sphere) : householder σ e0 = (σ : E) := by
  exact Submodule.reflection_sub (by simp [e0_norm])

theorem householder_involutive (σ : Sphere) (y : E) :
    householder σ (householder σ y) = y :=
  Submodule.reflection_reflection _ y

theorem householder_explicit (σ : Sphere) (y : E) :
    householder σ y =
      y - (2 * (inner ℝ (e0-(σ:E)) y / ‖e0-(σ:E)‖^2)) • (e0-(σ:E)) := by
  rw [householder, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp [neg_sub, two_smul, two_mul, add_smul]

theorem householder_joint_measurable :
    Measurable (fun x : Sphere × E => householder x.1 x.2) := by
  simp_rw [householder_explicit]
  fun_prop

theorem householder_preserves_volume (σ : Sphere) :
    MeasurePreserving (householder σ) (volume : Measure E) volume :=
  (householder σ).measurePreserving

def flatEmbedding (z : E2) : E := WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp z))

@[simp] theorem flatEmbedding_zero (z : E2) : flatEmbedding z 0 = 0 := rfl
@[simp] theorem flatEmbedding_succ (z : E2) (i : Fin 2) :
    flatEmbedding z i.succ = z i := rfl

theorem flatEmbedding_inner (z w : E2) :
    inner ℝ (flatEmbedding z) (flatEmbedding w) = inner ℝ z w := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, flatEmbedding]

def flatIsometry : E2 →ₗᵢ[ℝ] E where
  toLinearMap :=
    { toFun := flatEmbedding
      map_add' := by intro z w; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [flatEmbedding]
      map_smul' := by intro a z; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [flatEmbedding] }
  norm_map' z := by
    apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
    simpa only [real_inner_self_eq_norm_sq] using flatEmbedding_inner z z

/-- A measurable orthonormal plane chart, with no selected exceptional direction. -/
def planeIsometry (σ : Sphere) : E2 →ₗᵢ[ℝ] E :=
  (householder σ).toLinearIsometry.comp flatIsometry

@[simp] theorem planeIsometry_apply (σ : Sphere) (z : E2) :
    planeIsometry σ z = householder σ (flatEmbedding z) := rfl

def normalPlane (σ : Sphere) : Set E := {y | inner ℝ (σ : E) y = 0}

theorem planeIsometry_inner_normal (σ : Sphere) (z : E2) :
    inner ℝ (σ : E) (planeIsometry σ z) = 0 := by
  rw [← householder_e0 σ]
  change inner ℝ (householder σ e0) (householder σ (flatEmbedding z)) = 0
  rw [(householder σ).inner_map_map]
  simp [e0, PiLp.inner_apply, real_inner_apply, flatEmbedding]

theorem flat_range : Set.range flatIsometry = {y : E | y 0 = 0} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact flatEmbedding_zero z
  · intro hy
    let z : E2 := WithLp.toLp 2 (fun i : Fin 2 => y i.succ)
    refine ⟨z, ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hy.symm
    · rfl

theorem plane_range (σ : Sphere) :
    Set.range (planeIsometry σ) = normalPlane σ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact planeIsometry_inner_normal σ z
  · intro hy
    have hz : householder σ y ∈ Set.range flatIsometry := by
      rw [flat_range]
      change householder σ y 0 = 0
      have hh := (householder σ).inner_map_map (σ : E) y
      have hs : householder σ (σ : E) = e0 := by
        rw [← householder_e0 σ, householder_involutive]
      rw [hs] at hh
      have hz := hh.trans hy
      simpa [e0, PiLp.inner_apply] using hz
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    change householder σ (flatIsometry z) = y
    rw [hz, householder_involutive]

theorem flatEmbedding_measurable : Measurable flatEmbedding :=
  flatIsometry.continuous.measurable

def planePoint (σ : Sphere) (z : E2) : E := householder σ (flatEmbedding z)

theorem planePoint_eq (σ : Sphere) (z : E2) : planePoint σ z = planeIsometry σ z := rfl

theorem plane_joint_measurable :
    Measurable (fun p : Sphere × E2 => planePoint p.1 p.2) := by
  have hm : Measurable (fun p : Sphere × E2 => (p.1, flatEmbedding p.2)) :=
    measurable_fst.prodMk (flatEmbedding_measurable.comp measurable_snd)
  have hh := householder_joint_measurable.comp hm
  simpa only [Function.comp_def, planePoint] using hh

/-- The actual normalized Hausdorff plane area, not a measure chosen to fit a coarea formula. -/
def planeArea (σ : Sphere) : Measure E :=
  (Measure.euclideanHausdorffMeasure 2).restrict (normalPlane σ)

theorem planeArea_map_volume (σ : Sphere) :
    (volume : Measure E2).map (planeIsometry σ) = planeArea σ := by
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2]
  rw [(planeIsometry σ).isometry.map_euclideanHausdorffMeasure, plane_range]
  rfl

theorem planeArea_preserving (σ : Sphere) :
    MeasurePreserving (planeIsometry σ) (volume : Measure E2) (planeArea σ) :=
  ⟨(planeIsometry σ).continuous.measurable, planeArea_map_volume σ⟩

def splitCoords : E ≃ᵐ ℝ × E2 :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem splitCoords_apply (y : E) :
    splitCoords y = (y 0, WithLp.toLp 2 (fun j : Fin 2 => y j.succ)) := by
  rfl

theorem splitCoords_symm (t : ℝ) (z : E2) :
    splitCoords.symm (t,z) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) := by
  apply splitCoords.injective
  rw [splitCoords.apply_symm_apply, splitCoords_apply]
  rfl

theorem splitCoords_preserving :
    MeasurePreserving splitCoords (volume : Measure E)
      ((volume : Measure ℝ).prod (volume : Measure E2)) := by
  exact (PiLp.volume_preserving_ofLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_toLp (Fin 2))))

def normalCoords (σ : Sphere) : (ℝ × E2) ≃ᵐ E :=
  splitCoords.symm.trans (householder σ).toMeasurableEquiv

theorem normalCoords_preserving (σ : Sphere) :
    MeasurePreserving (normalCoords σ)
      ((volume : Measure ℝ).prod (volume : Measure E2)) (volume : Measure E) :=
  splitCoords_preserving.symm.trans (householder_preserves_volume σ)

theorem normalCoords_zero (σ : Sphere) (z : E2) :
    normalCoords σ (0,z) = planeIsometry σ z := by
  change householder σ (splitCoords.symm (0,z)) = householder σ (flatEmbedding z)
  rw [splitCoords_symm]
  rfl

theorem normalCoords_inner (σ : Sphere) (t : ℝ) (z : E2) :
    inner ℝ (σ : E) (normalCoords σ (t,z)) = t := by
  rw [← householder_e0 σ]
  change inner ℝ (householder σ e0) (householder σ (splitCoords.symm (t,z))) = t
  rw [(householder σ).inner_map_map]
  rw [splitCoords_symm]
  simp [e0, PiLp.inner_apply, real_inner_apply]

theorem normalCoords_formula (σ : Sphere) (t : ℝ) (z : E2) :
    normalCoords σ (t,z) = t • (σ : E) + planePoint σ z := by
  have hf : splitCoords.symm (t,z) = t • e0 + flatEmbedding z := by
    rw [splitCoords_symm]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [e0, flatEmbedding]
  change householder σ (splitCoords.symm (t,z)) = _
  rw [hf, map_add, map_smul, householder_e0]
  rfl

theorem normalCoords_joint_measurable :
    Measurable (fun p : Sphere × (ℝ × E2) => normalCoords p.1 p.2) := by
  have hm : Measurable (fun p : Sphere × (ℝ × E2) => (p.1,p.2.2)) := by fun_prop
  have hp' := plane_joint_measurable.comp hm
  have hp : Measurable (fun p : Sphere × (ℝ × E2) => planePoint p.1 p.2.2) := by
    simpa only [Function.comp_def] using hp' 
  simp_rw [show ∀ p : Sphere × (ℝ × E2),
    normalCoords p.1 p.2 = p.2.1 • (p.1 : E) + planePoint p.1 p.2.2 from
      fun p => normalCoords_formula p.1 p.2.1 p.2.2]
  exact (measurable_fst.comp measurable_snd).smul
    (measurable_subtype_coe.comp measurable_fst) |>.add hp

theorem normalCoords_continuous (σ : Sphere) :
    Continuous (fun p : ℝ × E2 => normalCoords σ p) := by
  have h (p : ℝ × E2) :
      normalCoords σ p = p.1 • (σ : E) + planeIsometry σ p.2 := by
    exact normalCoords_formula σ p.1 p.2
  simp_rw [h]
  exact (continuous_fst.smul continuous_const).add
    ((planeIsometry σ).continuous.comp continuous_snd)

theorem normalCoords_norm_sq (σ : Sphere) (t : ℝ) (z : E2) :
    ‖normalCoords σ (t,z)‖ ^ 2 = t^2 + ‖z‖^2 := by
  rw [normalCoords_formula, planePoint_eq, norm_add_sq_real, real_inner_smul_left,
    planeIsometry_inner_normal, (planeIsometry σ).norm_map]
  simp [norm_smul, sq_abs]

theorem normalCoords_transverse_bound (σ : Sphere) (t : ℝ) (z : E2) :
    ‖z‖ ≤ ‖normalCoords σ (t,z)‖ := by
  have hh := normalCoords_norm_sq σ t z
  nlinarith [sq_nonneg t, norm_nonneg z, norm_nonneg (normalCoords σ (t,z))]

def rectangleFour (k x y : E) : FourMomenta := ![k,k+x+y,k+x,k+y]

theorem rectangleFour_continuous :
    Continuous (fun t : E × (E × E) => rectangleFour t.1 t.2.1 t.2.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [rectangleFour] <;> fun_prop

theorem rectangleFour_nine (z : CoareaNormalization.Nine) :
    rectangleFour (CoareaNormalization.momentumAt z 0)
      (CoareaNormalization.momentumAt z 1) (CoareaNormalization.momentumAt z 2) =
      RectangularCoordinates.rectangle z := rfl

theorem rectangleFour_energy (k x y : E) :
    CoareaNormalization.energy (rectangleFour k x y) = 2 * inner ℝ x y := by
  change ‖k‖^2 + ‖k+x+y‖^2 - ‖k+x‖^2 - ‖k+y‖^2 = _
  simp only [norm_add_sq_real, inner_add_left]
  ring

theorem normal_energy (k : E) (σ : Sphere) (r t : ℝ) (z : E2) :
    CoareaNormalization.energy (rectangleFour k (r • (σ : E)) (normalCoords σ (t,z))) =
      2 * r * t := by
  rw [rectangleFour_energy, real_inner_smul_left, normalCoords_inner]
  ring

/-- Linear normal-energy substitution with its actual Jacobian. -/
theorem normal_energy_change {r : ℝ} (hr : 0 < r) (F : ℝ → ℝ) :
    (∫ t : ℝ, F t) = (2*r)⁻¹ * ∫ e : ℝ, F (e/(2*r)) := by
  have hi := Measure.integral_comp_inv_mul_left F (2*r)
  have hpos : 0 < 2*r := by positivity
  simp only [smul_eq_mul, abs_of_pos hpos] at hi
  have hz : 2*r ≠ 0 := ne_of_gt hpos
  calc
    _ = (2*r)⁻¹ * ((2*r) * ∫ t : ℝ, F t) := by field_simp
    _ = (2*r)⁻¹ * ∫ e : ℝ, F ((2*r)⁻¹ * e) := by rw [hi]
    _ = _ := by simp only [div_eq_mul_inv, mul_comm]

theorem original_triple_rectangular_integrable {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Integrable (fun p : E × (E × E) =>
      PolarCoordinates.sharpLayer R c Φ (rectangleFour p.1 p.2.1 p.2.2))
      ((volume : Measure E).prod (volume.prod volume)) := by
  apply (PolarCoordinates.nineToTriple_integrable_iff _
    ((PolarCoordinates.sharpLayer_measurable R c hΦ.measurable).comp
      rectangleFour_continuous.measurable).aestronglyMeasurable).mp
  exact RectangularCoordinates.rectangle_sharp_layer_integrable hR c Φ hΦ

abbrev Ray := Sphere × Radius
abbrev NormalInput := E × (Ray × (ℝ × E2))

def rayMeasure : Measure Ray :=
  ResonantMeasure.surface.prod (Measure.volumeIoiPow 2)
def normalInputMeasure : Measure NormalInput :=
  (volume : Measure E).prod (rayMeasure.prod ((volume : Measure ℝ).prod (volume : Measure E2)))
instance : SigmaFinite rayMeasure := by unfold rayMeasure; infer_instance
instance : SigmaFinite normalInputMeasure := by unfold normalInputMeasure; infer_instance

def rayNormal (p : Ray × (ℝ × E2)) : E × E :=
  (PolarCoordinates.polarVector p.1, normalCoords p.1.1 p.2)

theorem rayNormal_measurable : Measurable rayNormal := by
  have hm : Measurable (fun p : Ray × (ℝ × E2) => (p.1.1,p.2)) := by fun_prop
  have hn := normalCoords_joint_measurable.comp hm
  have hn' : Measurable (fun p : Ray × (ℝ × E2) => normalCoords p.1.1 p.2) := by
    simpa only [Function.comp_def] using hn
  exact (PolarCoordinates.polarVector_preserves_volume.measurable.comp measurable_fst).prodMk hn'

theorem rayNormal_preserving :
    MeasurePreserving rayNormal
      (rayMeasure.prod ((volume : Measure ℝ).prod (volume : Measure E2)))
      ((volume : Measure E).prod volume) := by
  have hm : Measurable (Function.uncurry
      (fun q : Ray => fun tz : ℝ × E2 => normalCoords q.1 tz)) := by
    exact measurable_snd.comp rayNormal_measurable
  exact PolarCoordinates.polarVector_preserves_volume.skew_product hm
    (ae_of_all _ fun p => (normalCoords_preserving p.1).map_eq)

def fullNormal (p : NormalInput) : E × (E × E) := (p.1,rayNormal p.2)

theorem fullNormal_preserving :
    MeasurePreserving fullNormal normalInputMeasure
      ((volume : Measure E).prod (volume.prod volume)) :=
  (MeasurePreserving.id (volume : Measure E)).prod rayNormal_preserving

theorem actual_joint_normal_integrable {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Integrable (fun p : NormalInput => PolarCoordinates.sharpLayer R c Φ
      (rectangleFour p.1 (PolarCoordinates.polarVector p.2.1) (normalCoords p.2.1.1 p.2.2)))
      normalInputMeasure :=
  fullNormal_preserving.integrable_comp_of_integrable
    (original_triple_rectangular_integrable hR c Φ hΦ)

theorem full_normal_integral (F : E × (E × E) → ℝ)
    (hF : Integrable F ((volume : Measure E).prod (volume.prod volume))) :
    (∫ p, F p) = ∫ p, F (fullNormal p) ∂normalInputMeasure := by
  have hi := integral_map fullNormal_preserving.measurable.aemeasurable
    (fullNormal_preserving.map_eq.symm ▸ hF.aestronglyMeasurable)
  rwa [fullNormal_preserving.map_eq] at hi


/-! Exact types and logical dependency audit for the fixed normal geometry. -/
#check real_inner_apply
#print axioms real_inner_apply
#check e0_norm
#print axioms e0_norm
#check householder_e0
#print axioms householder_e0
#check householder_involutive
#print axioms householder_involutive
#check householder_explicit
#print axioms householder_explicit
#check householder_joint_measurable
#print axioms householder_joint_measurable
#check householder_preserves_volume
#print axioms householder_preserves_volume
#check flatEmbedding_zero
#print axioms flatEmbedding_zero
#check flatEmbedding_succ
#print axioms flatEmbedding_succ
#check flatEmbedding_inner
#print axioms flatEmbedding_inner
#check planeIsometry_apply
#print axioms planeIsometry_apply
#check planeIsometry_inner_normal
#print axioms planeIsometry_inner_normal
#check flat_range
#print axioms flat_range
#check plane_range
#print axioms plane_range
#check flatEmbedding_measurable
#print axioms flatEmbedding_measurable
#check planePoint_eq
#print axioms planePoint_eq
#check plane_joint_measurable
#print axioms plane_joint_measurable
#check planeArea_map_volume
#print axioms planeArea_map_volume
#check planeArea_preserving
#print axioms planeArea_preserving
#check splitCoords_apply
#print axioms splitCoords_apply
#check splitCoords_symm
#print axioms splitCoords_symm
#check splitCoords_preserving
#print axioms splitCoords_preserving
#check normalCoords_preserving
#print axioms normalCoords_preserving
#check normalCoords_zero
#print axioms normalCoords_zero
#check normalCoords_inner
#print axioms normalCoords_inner
#check normalCoords_formula
#print axioms normalCoords_formula
#check normalCoords_joint_measurable
#print axioms normalCoords_joint_measurable
#check normalCoords_continuous
#print axioms normalCoords_continuous
#check normalCoords_norm_sq
#print axioms normalCoords_norm_sq
#check normalCoords_transverse_bound
#print axioms normalCoords_transverse_bound
#check rectangleFour_continuous
#print axioms rectangleFour_continuous
#check rectangleFour_nine
#print axioms rectangleFour_nine
#check rectangleFour_energy
#print axioms rectangleFour_energy
#check normal_energy
#print axioms normal_energy
#check normal_energy_change
#print axioms normal_energy_change
#check original_triple_rectangular_integrable
#print axioms original_triple_rectangular_integrable
#check rayNormal_measurable
#print axioms rayNormal_measurable
#check rayNormal_preserving
#print axioms rayNormal_preserving
#check fullNormal_preserving
#print axioms fullNormal_preserving
#check actual_joint_normal_integrable
#print axioms actual_joint_normal_integrable
#check full_normal_integral
#print axioms full_normal_integral

end
end Resonance.PlaneCoarea
