import Resonance.CollisionFiber
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.TietzeExtension

/-!
The collision fibers are the actual disintegration of the independently normalized
full sharp four-leg resonance measure.  At each fixed output, all three moving
input faces are null; the output flag stays true along the original closed cube.
This gives a pointwise continuous representative, including faces and corners.
Tietze extension is used only after proving that all off-cube values are irrelevant.
The resulting C(D_R) map retains all four cubic parents and is locally Lipschitz.
-/

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal EuclideanGeometry Pointwise ProbabilityTheory

namespace Resonance.FiberContinuity
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea Resonance.PlaneGlobal Resonance.CollisionFiber

theorem sphere_coordinate_zero_null (j : Fin 3) :
    ResonantMeasure.surface {σ : Sphere | (σ:E) j = 0} = 0 := by
  have hs : MeasurableSet {σ : Sphere | (σ:E) j = 0} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [ResonantMeasure.surface,Measure.toSphere_apply' _ hs]
  have hsub : Ioo (0:ℝ) 1 • ((↑) '' {σ : Sphere | (σ:E) j=0}) ⊆
      {x : E | x j=0} := by
    rintro x ⟨r,hr,y,⟨σ,hσ,rfl⟩,rfl⟩
    change r * (σ:E) j = 0
    change (σ:E) j = 0 at hσ
    rw [hσ,mul_zero]
  rw [measure_mono_null hsub (CoareaGlobal.euclidean_coordinate_face_null j 0),mul_zero]

theorem sphere_norm_coordinates (σ : Sphere) :
    (σ:E) 0 ^ 2 + (σ:E) 1 ^ 2 + (σ:E) 2 ^ 2 = 1 := by
  have h : inner ℝ (σ:E) (σ:E) = 1 := by
    rw [real_inner_self_eq_norm_sq,ResonantMeasure.sphere_norm]
    norm_num
  rw [PiLp.inner_apply] at h
  simp only [real_inner_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h
  change (σ:E) 0 * (σ:E) 0 + ((σ:E) 1 * (σ:E) 1 + (σ:E) 2 * (σ:E) 2) = 1 at h
  nlinarith [h]

theorem sphere_coordinate_extreme_null (j : Fin 3) :
    ResonantMeasure.surface {σ : Sphere | (σ:E) j ^ 2 = 1} = 0 := by
  fin_cases j
  · apply measure_mono_null (t := {σ : Sphere | (σ:E) 1 = 0})
    · intro σ hσ
      change (σ:E) 1 = 0
      have hn := sphere_norm_coordinates σ
      change (σ:E) 0^2=1 at hσ
      nlinarith [sq_nonneg ((σ:E) 1),sq_nonneg ((σ:E) 2)]
    · exact sphere_coordinate_zero_null 1
  · apply measure_mono_null (t := {σ : Sphere | (σ:E) 0 = 0})
    · intro σ hσ
      change (σ:E) 0 = 0
      have hn := sphere_norm_coordinates σ
      change (σ:E) 1^2=1 at hσ
      nlinarith [sq_nonneg ((σ:E) 0),sq_nonneg ((σ:E) 2)]
    · exact sphere_coordinate_zero_null 0
  · apply measure_mono_null (t := {σ : Sphere | (σ:E) 0 = 0})
    · intro σ hσ
      change (σ:E) 0 = 0
      have hn := sphere_norm_coordinates σ
      change (σ:E) 2^2=1 at hσ
      nlinarith [sq_nonneg ((σ:E) 0),sq_nonneg ((σ:E) 1)]
    · exact sphere_coordinate_zero_null 0

theorem sphere_coordinate_generic_ae (j : Fin 3) :
    ∀ᵐ σ : Sphere ∂(ResonantMeasure.surface), (σ:E) j ^ 2 ≠ 1 := by
  apply ae_iff.mpr
  simpa only [not_not] using sphere_coordinate_extreme_null j

def planeCoordinate (σ : Sphere) (j : Fin 3) : E2 →ₗ[ℝ] ℝ where
  toFun z := planeIsometry σ z j
  map_add' z w := congrArg (fun v : E => v j) ((planeIsometry σ).map_add z w)
  map_smul' a z := congrArg (fun v : E => v j) ((planeIsometry σ).map_smul a z)

theorem planeCoordinate_nonzero (σ : Sphere) (j : Fin 3)
    (hσ : (σ:E) j ^ 2 ≠ 1) : ∃ z : E2, planeCoordinate σ j z ≠ 0 := by
  let y : E := EuclideanSpace.single j 1 - ((σ:E) j) • (σ:E)
  have hn : inner ℝ (σ:E) (σ:E) = 1 := by
    rw [real_inner_self_eq_norm_sq,ResonantMeasure.sphere_norm]
    norm_num
  have hs : inner ℝ (σ:E) (EuclideanSpace.single j 1) = (σ:E) j := by
    simp [PiLp.inner_apply,real_inner_apply]
  have hy : y∈normalPlane σ := by
    change inner ℝ (σ:E) y = 0
    simp [y,inner_sub_right,inner_smul_right,hs]
  obtain ⟨z,hz⟩ := (plane_range σ).symm ▸ hy
  refine ⟨z,?_⟩
  change planeIsometry σ z j ≠ 0
  rw [hz]
  have hyj : y j = 1 - (σ:E) j * (σ:E) j := by simp [y]
  rw [hyj]
  intro hz
  apply hσ
  nlinarith

theorem nonzero_linear_level_null (L : E2 →ₗ[ℝ] ℝ)
    (hL : ∃ z, L z ≠ 0) (a : ℝ) :
    (volume : Measure E2) {z | L z = a} = 0 := by
  let S : AffineSubspace ℝ E2 := (affineSpan ℝ ({a}:Set ℝ)).comap L.toAffineMap
  have hn : S ≠ ⊤ := by
    intro ht
    have hall (z : E2) : L z=a := by
      have hz : z∈S := by rw [ht]; trivial
      simpa [S] using hz
    obtain ⟨z,hz⟩ := hL
    exact hz ((hall z).trans (by simpa using (hall 0).symm))
  simpa [S] using Measure.addHaar_affineSubspace (volume : Measure E2) S hn

theorem plane_coordinate_level_null (σ : Sphere) (j : Fin 3)
    (hσ : (σ:E) j ^ 2 ≠ 1) (a : ℝ) :
    (volume : Measure E2) {z | planePoint σ z j=a} = 0 :=
  nonzero_linear_level_null (planeCoordinate σ j) (planeCoordinate_nonzero σ j hσ) a

theorem rayOne_absolutelyContinuous : rayOne ≪ rayMeasure := by
  rw [rayMeasure_from_rayOne]
  apply withDensity_absolutelyContinuous' (by fun_prop)
  apply ae_of_all
  intro p
  exact ne_of_gt (ENNReal.ofReal_pos.mpr p.2.property)

theorem ray_coordinate_level_null (k : E) (j : Fin 3) (a : ℝ) :
    rayOne {p : Ray | k j + PolarCoordinates.polarVector p j = a} = 0 := by
  have hs : MeasurableSet {x : E | x j = a-k j} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hz := PolarCoordinates.polarVector_preserves_volume.measure_preimage hs.nullMeasurableSet
  have he : {p : Ray | k j + PolarCoordinates.polarVector p j = a} =
      PolarCoordinates.polarVector ⁻¹' {x : E | x j = a-k j} := by
    ext p
    change (k j + PolarCoordinates.polarVector p j=a) ↔
      PolarCoordinates.polarVector p j=a-k j
    constructor <;> intro h <;> linarith
  apply rayOne_absolutelyContinuous
  rw [he,rayMeasure,hz]
  exact CoareaGlobal.euclidean_coordinate_face_null j (a-k j)

theorem ray_coordinate_generic_ae (j : Fin 3) :
    ∀ᵐ p : Ray ∂rayOne, (p.1:E) j ^ 2 ≠ 1 := by
  rw [rayOne]
  have hm : MeasurableSet {p : Ray | (p.1:E) j^2≠1} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).compl
  apply (Measure.ae_prod_iff_ae_ae hm).2
  filter_upwards [sphere_coordinate_generic_ae j] with σ hσ
  exact ae_of_all _ (fun _ => hσ)

theorem shifted_plane_level_null (j : Fin 3) (a : ℝ) (offset : Ray → ℝ)
    (hoffset : Measurable offset) :
    fiberBase {b : FiberParameters | offset b.1 + planePoint b.1.1 b.2 j = a} = 0 := by
  have hp := plane_joint_measurable.comp
    (show Measurable (fun b : FiberParameters => (b.1.1,b.2)) by fun_prop)
  have hc : Measurable (fun b : FiberParameters => planePoint b.1.1 b.2 j) :=
    (by fun_prop : Measurable (fun x : E => x j)).comp hp
  have hs : MeasurableSet {b : FiberParameters |
      offset b.1 + planePoint b.1.1 b.2 j = a} :=
    measurableSet_eq_fun ((hoffset.comp measurable_fst).add hc) measurable_const
  rw [fiberBase,Measure.prod_apply hs]
  have he : ∀ᵐ p : Ray ∂rayOne,
      (volume : Measure E2) ((Prod.mk p) ⁻¹'
        {b : FiberParameters | offset b.1 + planePoint b.1.1 b.2 j = a}) = 0 := by
    filter_upwards [ray_coordinate_generic_ae j] with p hp
    have hs' : ((Prod.mk p) ⁻¹'
        {b : FiberParameters | offset b.1 + planePoint b.1.1 b.2 j = a}) =
        {z : E2 | planePoint p.1 z j = a-offset p} := by
      ext z
      change (offset p + planePoint p.1 z j=a) ↔ planePoint p.1 z j=a-offset p
      constructor <;> intro h <;> linarith
    rw [hs']
    exact plane_coordinate_level_null p.1 j hp (a-offset p)
  rw [lintegral_congr_ae he,lintegral_zero]

theorem fiberFour_one (k : E) (b : FiberParameters) :
    fiberFour k b 1 = k + PolarCoordinates.polarVector b.1 + planePoint b.1.1 b.2 := by
  simp [fiberFour,planeShell,rectangleFour,normalCoords_zero,planePoint_eq,
    PolarCoordinates.polarVector,add_assoc]

theorem fiberFour_two (k : E) (b : FiberParameters) :
    fiberFour k b 2 = k + PolarCoordinates.polarVector b.1 := rfl

theorem fiberFour_three (k : E) (b : FiberParameters) :
    fiberFour k b 3 = k + planePoint b.1.1 b.2 := by
  simp [fiberFour,planeShell,rectangleFour,normalCoords_zero,planePoint_eq]

/-- Fixed-output face nullity is proved before integrating over the output momentum. -/
theorem fiber_leg_level_null (k : E) (i : Fin 4) (hi : i≠0) (j : Fin 3) (a : ℝ) :
    fiberBase {b : FiberParameters | fiberFour k b i j = a} = 0 := by
  fin_cases i
  · exact (hi rfl).elim
  · change fiberBase {b : FiberParameters | fiberFour k b 1 j=a} = 0
    have he : {b : FiberParameters | fiberFour k b 1 j=a} =
        {b : FiberParameters | (k j + PolarCoordinates.polarVector b.1 j) +
          planePoint b.1.1 b.2 j=a} := by
      ext b
      simp only [fiberFour_one,PiLp.add_apply]
    rw [he]
    exact shifted_plane_level_null j a (fun p => k j+PolarCoordinates.polarVector p j) (by
      exact measurable_const.add
        ((by fun_prop : Measurable (fun x : E => x j)).comp
          PolarCoordinates.polarVector_preserves_volume.measurable))
  · change fiberBase {b : FiberParameters | fiberFour k b 2 j=a} = 0
    have he : {b : FiberParameters | fiberFour k b 2 j=a} =
        {p : Ray | k j+PolarCoordinates.polarVector p j=a} ×ˢ (univ : Set E2) := by
      ext b
      simp only [fiberFour_two,PiLp.add_apply,mem_setOf_eq,mem_prod,mem_univ,and_true]
    rw [he,fiberBase,Measure.prod_prod,ray_coordinate_level_null k j a,zero_mul]
  · change fiberBase {b : FiberParameters | fiberFour k b 3 j=a} = 0
    have he : {b : FiberParameters | fiberFour k b 3 j=a} =
        {b : FiberParameters | k j + planePoint b.1.1 b.2 j=a} := by
      ext b
      simp only [fiberFour_three,PiLp.add_apply]
    rw [he]
    exact shifted_plane_level_null j a _ measurable_const

theorem fiber_nonoutput_faces_avoided (k : E) (R : ℝ) :
    ∀ᵐ b : FiberParameters ∂fiberBase, ∀ i : Fin 4, i≠0 →
      ∀ j : Fin 3, |fiberFour k b i j| ≠ R := by
  apply Filter.eventually_all.2
  intro i
  by_cases hi : i=0
  · exact ae_of_all _ (fun _ h => (h hi).elim)
  · apply Filter.Eventually.mono ?_ (fun _ h _ => h)
    apply Filter.eventually_all.2
    intro j
    apply ae_iff.mpr
    have hsub : {b : FiberParameters | ¬|fiberFour k b i j| ≠ R} ⊆
        {b | fiberFour k b i j=R} ∪ {b | fiberFour k b i j= -R} := by
      intro b hb
      have hh : |fiberFour k b i j|=R := not_not.mp hb
      rcases le_total 0 (fiberFour k b i j) with hpos | hneg
      · exact Or.inl (by simpa only [abs_of_nonneg hpos] using hh)
      · exact Or.inr (by
          change fiberFour k b i j= -R
          rw [abs_of_nonpos hneg] at hh
          linarith)
    exact measure_mono_null hsub
      (measure_union_null (fiber_leg_level_null k i hi j R) (fiber_leg_level_null k i hi j (-R)))

theorem fiberFour_continuous (b : FiberParameters) : Continuous (fun k : E => fiberFour k b) := by
  apply continuous_pi
  intro i
  simp only [fiberFour,planeShell_translate]
  fun_prop

theorem coordinate_threshold_eventually {f : E → ℝ} {k : E} {a : ℝ}
    (hf : ContinuousAt f k) (hne : f k≠a) :
    ∀ᶠ p in nhds k, (f p≤a ↔ f k≤a) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he := hf.tendsto.eventually (isOpen_Iio.mem_nhds hlt)
    filter_upwards [he] with p hp
    exact iff_of_true (le_of_lt hp) hlt.le
  · have he := hf.tendsto.eventually (isOpen_Ioi.mem_nhds hgt)
    filter_upwards [he] with p hp
    exact iff_of_false (not_le_of_gt hp) (not_le_of_gt hgt)

theorem fiberSharp_continuousWithinAt (R : ℝ) (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (k : E) (hk : k∈ResonantMeasure.cube R) (b : FiberParameters)
    (hb : ∀ i : Fin 4, i≠0 → ∀ j : Fin 3, |fiberFour k b i j|≠R) :
    ContinuousWithinAt (fun p : E => CoareaNormalization.sharpReadout R Φ (fiberFour p b))
      (ResonantMeasure.cube R) k := by
  have hc := fiberFour_continuous b
  have hcoords : ∀ᶠ p in nhds k, ∀ i : Fin 4, i≠0 → ∀ j : Fin 3,
      (|fiberFour p b i j|≤R ↔ |fiberFour k b i j|≤R) := by
    apply Filter.eventually_all.2
    intro i
    by_cases hi : i=0
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · apply Filter.Eventually.mono ?_ (fun _ h _ => h)
      apply Filter.eventually_all.2
      intro j
      have hout : Continuous (fun q : FourMomenta => |q i j|) := by fun_prop
      exact coordinate_threshold_eventually
        (k := k) (a := R) (hout.comp hc).continuousAt (hb i hi j)
  have hflags : ∀ᶠ p in nhdsWithin k (ResonantMeasure.cube R),
      (fiberFour p b∈CoareaNormalization.allFourFlags R ↔
       fiberFour k b∈CoareaNormalization.allFourFlags R) := by
    filter_upwards [hcoords.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with p hp hpD
    change (∀ i,∀ j,|fiberFour p b i j|≤R) ↔ (∀ i,∀ j,|fiberFour k b i j|≤R)
    apply forall_congr'
    intro i
    by_cases hi : i=0
    · subst i
      simpa only [fiberFour_output] using (iff_of_true hpD hk)
    · exact forall_congr' (fun j => hp i hi j)
  by_cases h0 : fiberFour k b∈CoareaNormalization.allFourFlags R
  · have heq : (fun p : E => CoareaNormalization.sharpReadout R Φ (fiberFour p b))
        =ᶠ[nhdsWithin k (ResonantMeasure.cube R)] (fun p => Φ (fiberFour p b)) := by
      filter_upwards [hflags] with p hp
      exact Set.indicator_of_mem (hp.mpr h0) Φ
    change Filter.Tendsto _ _ (nhds (CoareaNormalization.sharpReadout R Φ (fiberFour k b)))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem h0]
    exact (hΦ.comp hc).continuousAt.continuousWithinAt.tendsto.congr' heq.symm
  · have heq : (fun p : E => CoareaNormalization.sharpReadout R Φ (fiberFour p b))
        =ᶠ[nhdsWithin k (ResonantMeasure.cube R)] (fun _ => (0:ℝ)) := by
      filter_upwards [hflags] with p hp
      exact Set.indicator_of_notMem (fun h => h0 (hp.mp h)) Φ
    change Filter.Tendsto _ _ (nhds (CoareaNormalization.sharpReadout R Φ (fiberFour k b)))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem h0]
    exact tendsto_const_nhds.congr' heq.symm

def fiberReadout (R : ℝ) (Φ : FourMomenta → ℝ) (k : E) : ℝ :=
  ∫ q, Φ q ∂fiberMeasure R k

theorem fiberReadout_base (R : ℝ) (Φ : FourMomenta → ℝ) (hΦ : Measurable Φ) (k : E) :
    fiberReadout R Φ k = (1/2:ℝ) *
      ∫ b, CoareaNormalization.sharpReadout R Φ (fiberFour k b) ∂fiberBase := by
  rw [fiberReadout,fiberMeasure,integral_smul_measure,
    integral_map (fiberFour_measurable k).aemeasurable hΦ.aestronglyMeasurable]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  congr 1
  rw [← integral_indicator (fiberAllowed_measurable R k)]
  apply integral_congr_ae
  apply ae_of_all
  intro b
  by_cases hb : b∈fiberAllowed R k
  · rw [Set.indicator_of_mem hb]
    exact (Set.indicator_of_mem
      (show fiberFour k b∈CoareaNormalization.allFourFlags R from hb) Φ).symm
  · rw [Set.indicator_of_notMem hb]
    exact (Set.indicator_of_notMem
      (show fiberFour k b∉CoareaNormalization.allFourFlags R from hb) Φ).symm

def finiteFiberBase (R : ℝ) : Measure FiberParameters := fiberBase.restrict (fiberBox R)
instance (R : ℝ) : IsFiniteMeasure (finiteFiberBase R) :=
  ⟨by simpa [finiteFiberBase] using fiberBox_finite R⟩

theorem fiberReadout_box {R : ℝ} (hR : 0≤R) (Φ : FourMomenta → ℝ)
    (hΦ : Measurable Φ) (k : E) :
    fiberReadout R Φ k = (1/2:ℝ) *
      ∫ b, CoareaNormalization.sharpReadout R Φ (fiberFour k b) ∂finiteFiberBase R := by
  rw [fiberReadout_base R Φ hΦ k]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro b hb
  exact Set.indicator_of_notMem
    (show fiberFour k b ∉ CoareaNormalization.allFourFlags R from
      fun h => hb (fiberAllowed_subset_box hR k h)) Φ

theorem fiberSharp_bound {R B : ℝ} (hB : 0≤B) (Φ : FourMomenta → ℝ)
    (hΦ : ∀ q∈CoareaNormalization.allFourFlags R, ‖Φ q‖≤B) (k : E) (b : FiberParameters) :
    ‖CoareaNormalization.sharpReadout R Φ (fiberFour k b)‖ ≤ B := by
  by_cases h : fiberFour k b∈CoareaNormalization.allFourFlags R
  · rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem h]
    exact hΦ _ h
  · rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem h,norm_zero]
    exact hB

/-- Continuity is on the original closed cube, including every face and corner. -/
theorem fiberReadout_continuousOn {R : ℝ} (hR : 0≤R) (Φ : FourMomenta → ℝ)
    (hΦ : Continuous Φ) : ContinuousOn (fiberReadout R Φ) (ResonantMeasure.cube R) := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  have hrepr : fiberReadout R Φ = fun k => (1/2:ℝ) *
      ∫ b, CoareaNormalization.sharpReadout R Φ (fiberFour k b) ∂finiteFiberBase R :=
    funext (fiberReadout_box hR Φ hΦ.measurable)
  rw [hrepr]
  intro k hk
  apply ContinuousWithinAt.mul continuousWithinAt_const
  change Filter.Tendsto _ (nhdsWithin k (ResonantMeasure.cube R)) _
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : FiberParameters => B)
  · exact Filter.Eventually.of_forall (fun p =>
      ((CoareaNormalization.sharpReadout_measurable R hΦ.measurable).comp
        (fiberFour_measurable p)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun p => ae_of_all _ (fiberSharp_bound hB Φ hbound p))
  · exact integrable_const B
  · have ha := ae_restrict_of_ae (s := fiberBox R) (fiber_nonoutput_faces_avoided k R)
    filter_upwards [ha] with b hb
    exact (fiberSharp_continuousWithinAt R Φ hΦ k hk b hb).tendsto

theorem cube_isClosed (R : ℝ) : IsClosed (ResonantMeasure.cube R) := by
  change IsClosed {k : E | ∀ j, |k j| ≤ R}
  simpa only [Set.setOf_forall] using
    (isClosed_iInter (fun j : Fin 3 =>
      isClosed_le (show Continuous (fun k : E => |k j|) by fun_prop)
        continuous_const))

theorem cube_isCompact (R : ℝ) : IsCompact (ResonantMeasure.cube R) := by
  apply (isCompact_closedBall (0:E) (3*|R|)).of_isClosed_subset (cube_isClosed R)
  intro k hk
  have h := ResonantMeasure.norm_le_three_R (abs_nonneg R)
    (show k∈ResonantMeasure.cube |R| from fun j => (hk j).trans (le_abs_self R))
  simpa [mem_closedBall,dist_zero_right] using h

instance cube_compactSpace (R : ℝ) : CompactSpace (ResonantMeasure.cube R) :=
  isCompact_iff_compactSpace.mp (cube_isCompact R)

/-- Values outside the original four flags never affect the actual fiber output. -/
theorem collisionOutput_congr_on_cube (R : ℝ) (f g : E → ℝ)
    (hfg : ∀ k∈ResonantMeasure.cube R, f k=g k) :
    collisionOutput R f = collisionOutput R g := by
  funext k
  apply integral_congr_ae
  filter_upwards [fiber_support R k] with q hq
  have heq : (fun i => f (q i)) = (fun i => g (q i)) :=
    funext (fun i => hfg _ (hq.1 i))
  exact congrArg Collision.collisionPolynomial heq

theorem collisionIntegrand_continuous {f : E → ℝ} (hf : Continuous f) :
    Continuous (collisionIntegrand f) := by
  unfold collisionIntegrand Collision.collisionPolynomial
  fun_prop

/-- Only continuity on the closed cube is needed; its zero extension can jump. -/
theorem collisionOutput_continuousOn {R : ℝ} (hR : 0≤R) (f : E → ℝ)
    (hf : ContinuousOn f (ResonantMeasure.cube R)) :
    ContinuousOn (collisionOutput R f) (ResonantMeasure.cube R) := by
  let fc : C(ResonantMeasure.cube R,ℝ) :=
    ⟨fun k => f k,continuousOn_iff_continuous_restrict.mp hf⟩
  obtain ⟨g,hg⟩ := fc.exists_restrict_eq (cube_isClosed R)
  have hfg : ∀ k∈ResonantMeasure.cube R, f k=g k := by
    intro k hk
    exact (congrArg (fun z : C(ResonantMeasure.cube R,ℝ) => z ⟨k,hk⟩) hg).symm
  rw [collisionOutput_congr_on_cube R f g hfg]
  exact fiberReadout_continuousOn hR _ (collisionIntegrand_continuous g.continuous)

/-- A genuine continuous extension, used only to define a cube representative. -/
def continuousExtension (R : ℝ) (f : C(ResonantMeasure.cube R,ℝ)) : C(E,ℝ) :=
  Classical.choose (f.exists_restrict_eq (cube_isClosed R))

theorem continuousExtension_eq (R : ℝ) (f : C(ResonantMeasure.cube R,ℝ))
    (k : ResonantMeasure.cube R) : continuousExtension R f k=f k :=
  congrArg (fun z : C(ResonantMeasure.cube R,ℝ) => z k)
    (Classical.choose_spec (f.exists_restrict_eq (cube_isClosed R)))

/-- The original collision polynomial defines an actual map on the Banach space C(D_R). -/
def collisionMap (R : ℝ) (hR : 0≤R) (f : C(ResonantMeasure.cube R,ℝ)) :
    C(ResonantMeasure.cube R,ℝ) :=
  ⟨fun k => collisionOutput R (continuousExtension R f) k,
    continuousOn_iff_continuous_restrict.mp
      (collisionOutput_continuousOn hR _ (continuousExtension R f).continuous.continuousOn)⟩

theorem collisionMap_apply (R : ℝ) (hR : 0≤R) (f : C(ResonantMeasure.cube R,ℝ))
    (g : E → ℝ) (hg : ∀ k : ResonantMeasure.cube R, g k=f k)
    (k : ResonantMeasure.cube R) : collisionMap R hR f k=collisionOutput R g k := by
  change collisionOutput R (continuousExtension R f) k=collisionOutput R g k
  rw [collisionOutput_congr_on_cube R (continuousExtension R f) g (fun p hp =>
    (continuousExtension_eq R f ⟨p,hp⟩).trans (hg ⟨p,hp⟩).symm)]

theorem collisionMap_norm_le (R : ℝ) (hR : 0≤R) (f : C(ResonantMeasure.cube R,ℝ)) :
    ‖collisionMap R hR f‖ ≤ 4*‖f‖^3*(fiberMassBound R).toReal := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro k
  apply collisionOutput_bound hR (norm_nonneg f) _
  intro p hp
  rw [continuousExtension_eq R f ⟨p,hp⟩]
  exact f.norm_coe_le_norm ⟨p,hp⟩

/-- Three-factor telescoping on the very same input values. -/
theorem triple_difference_bound {M L a b d a' b' d' : ℝ}
    (hM : 0≤M) (hL : 0≤L)
    (_ha : ‖a‖≤M) (hb : ‖b‖≤M) (hd : ‖d‖≤M)
    (ha' : ‖a'‖≤M) (hb' : ‖b'‖≤M) (_hd' : ‖d'‖≤M)
    (hda : ‖a-a'‖≤L) (hdb : ‖b-b'‖≤L) (hdd : ‖d-d'‖≤L) :
    ‖a*b*d-a'*b'*d'‖ ≤ 3*M^2*L := by
  have h1 : ‖(a-a')*b*d‖ ≤ L*M*M := by
    simp only [norm_mul]
    gcongr
  have h2 : ‖a'*(b-b')*d‖ ≤ M*L*M := by
    simp only [norm_mul]
    gcongr
  have h3 : ‖a'*b'*(d-d')‖ ≤ M*M*L := by
    simp only [norm_mul]
    gcongr
  rw [show a*b*d-a'*b'*d'=(a-a')*b*d+a'*(b-b')*d+a'*b'*(d-d') by ring]
  calc
    _ ≤ ‖(a-a')*b*d+a'*(b-b')*d‖+‖a'*b'*(d-d')‖ := norm_add_le _ _
    _ ≤ (‖(a-a')*b*d‖+‖a'*(b-b')*d‖)+‖a'*b'*(d-d')‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ L*M*M+M*L*M+M*M*L := add_le_add (add_le_add h1 h2) h3
    _ = 3*M^2*L := by ring

/-- All four gain/loss parents are retained in this local Lipschitz estimate. -/
theorem collisionPolynomial_difference_bound {M L : ℝ} (hM : 0≤M) (hL : 0≤L)
    (a b : Fin 4 → ℝ) (ha : ∀ i,‖a i‖≤M) (hb : ∀ i,‖b i‖≤M)
    (hd : ∀ i,‖a i-b i‖≤L) :
    ‖Collision.collisionPolynomial a-Collision.collisionPolynomial b‖ ≤ 12*M^2*L := by
  let t := fun i j k => a i*a j*a k-b i*b j*b k
  have ht : ∀ i j k, ‖t i j k‖ ≤ 3*M^2*L := fun i j k =>
    triple_difference_bound hM hL (ha i) (ha j) (ha k)
      (hb i) (hb j) (hb k) (hd i) (hd j) (hd k)
  have heq : Collision.collisionPolynomial a-Collision.collisionPolynomial b =
      t 1 2 3+t 0 2 3-t 0 1 3-t 0 1 2 := by
    unfold Collision.collisionPolynomial t
    ring
  rw [heq]
  have h1 := norm_add_le (t 1 2 3) (t 0 2 3)
  have h2 := norm_sub_le (t 1 2 3+t 0 2 3) (t 0 1 3)
  have h3 := norm_sub_le (t 1 2 3+t 0 2 3-t 0 1 3) (t 0 1 2)
  linarith [ht 1 2 3,ht 0 2 3,ht 0 1 3,ht 0 1 2]

theorem collisionOutput_difference_bound {R M L : ℝ} (hR : 0≤R)
    (hM : 0≤M) (hL : 0≤L) (f g : E → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M)
    (hg : ∀ k∈ResonantMeasure.cube R, ‖g k‖≤M)
    (hd : ∀ k∈ResonantMeasure.cube R, ‖f k-g k‖≤L) (k : E) :
    ‖collisionOutput R f k-collisionOutput R g k‖ ≤
      12*M^2*L*(fiberMassBound R).toReal := by
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  rw [collisionOutput,collisionOutput,← integral_sub
    (collisionIntegrand_integrable hR hM f hfm hf k)
    (collisionIntegrand_integrable hR hM g hgm hg k)]
  apply le_trans (norm_integral_le_of_norm_le_const (C := 12*M^2*L) ?_)
  · exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (fiberMassBound_lt_top R).ne (fiberMeasure_mass_le hR k))
      (by positivity)
  · filter_upwards [fiber_support R k] with q hq
    exact collisionPolynomial_difference_bound hM hL _ _
      (fun i => hf _ (hq.1 i)) (fun i => hg _ (hq.1 i)) (fun i => hd _ (hq.1 i))

/-- Quantitative Banach-space local Lipschitz estimate on every norm ball. -/
theorem collisionMap_sub_norm_le {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f g : C(ResonantMeasure.cube R,ℝ)) (hf : ‖f‖≤M) (hg : ‖g‖≤M) :
    ‖collisionMap R hR f-collisionMap R hR g‖ ≤
      (12*M^2*(fiberMassBound R).toReal)*‖f-g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro k
  change ‖collisionOutput R (continuousExtension R f) k-
      collisionOutput R (continuousExtension R g) k‖ ≤ _
  have hb f (hf : ‖f‖≤M) : ∀ p∈ResonantMeasure.cube R,
      ‖continuousExtension R f p‖≤M := by
    intro p hp
    rw [continuousExtension_eq R f ⟨p,hp⟩]
    exact (f.norm_coe_le_norm ⟨p,hp⟩).trans hf
  have hd : ∀ p∈ResonantMeasure.cube R,
      ‖continuousExtension R f p-continuousExtension R g p‖≤‖f-g‖ := by
    intro p hp
    rw [continuousExtension_eq R f ⟨p,hp⟩,continuousExtension_eq R g ⟨p,hp⟩]
    exact (f-g).norm_coe_le_norm ⟨p,hp⟩
  have h := collisionOutput_difference_bound hR hM (norm_nonneg (f-g)) _ _
    (continuousExtension R f).continuous.measurable (continuousExtension R g).continuous.measurable
    (hb f hf) (hb g hg) hd (k:E)
  convert h using 1
  ring

theorem collisionMap_lipschitzOnWith {R M : ℝ} (hR : 0≤R) (hM : 0≤M) :
    LipschitzOnWith ⟨12*M^2*(fiberMassBound R).toReal,by positivity⟩
      (collisionMap R hR) (closedBall 0 M) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro f hf g hg
  have hf' : ‖f‖≤M := by simpa [mem_closedBall,dist_zero_right] using hf
  have hg' : ‖g‖≤M := by simpa [mem_closedBall,dist_zero_right] using hg
  simpa only [dist_eq_norm,NNReal.coe_mk] using collisionMap_sub_norm_le hR hM f g hf' hg'

theorem collisionMap_continuous {R : ℝ} (hR : 0≤R) : Continuous (collisionMap R hR) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  have hL := collisionMap_lipschitzOnWith hR (M := ‖f‖+1) (by positivity)
  apply hL.continuousOn.continuousAt
  apply Metric.closedBall_mem_nhds_of_mem
  simp [mem_ball,dist_zero_right]

theorem collisionMap_zero {R : ℝ} (hR : 0≤R) : collisionMap R hR 0=0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using collisionMap_norm_le R hR 0) (norm_nonneg _)

/-- Even an arbitrary off-cube representative has a genuinely integrable collision integrand. -/
theorem collisionIntegrand_integrable_continuousOn {R : ℝ} (hR : 0≤R)
    (f : E → ℝ) (hf : ContinuousOn f (ResonantMeasure.cube R)) (k : E) :
    Integrable (collisionIntegrand f) (fiberMeasure R k) := by
  let fc : C(ResonantMeasure.cube R,ℝ) :=
    ⟨fun p => f p,continuousOn_iff_continuous_restrict.mp hf⟩
  have hb : ∀ p∈ResonantMeasure.cube R, ‖continuousExtension R fc p‖≤‖fc‖ := by
    intro p hp
    rw [continuousExtension_eq R fc ⟨p,hp⟩]
    exact fc.norm_coe_le_norm ⟨p,hp⟩
  have hi := collisionIntegrand_integrable hR (norm_nonneg fc) _
    (continuousExtension R fc).continuous.measurable hb k
  apply hi.congr
  filter_upwards [fiber_support R k] with q hq
  apply congrArg Collision.collisionPolynomial
  funext i
  exact continuousExtension_eq R fc ⟨q i,hq.1 i⟩

/-! Complete declaration types and logical dependency audit. -/
#check sphere_coordinate_zero_null
#print axioms sphere_coordinate_zero_null
#check sphere_norm_coordinates
#print axioms sphere_norm_coordinates
#check sphere_coordinate_extreme_null
#print axioms sphere_coordinate_extreme_null
#check sphere_coordinate_generic_ae
#print axioms sphere_coordinate_generic_ae
#check planeCoordinate_nonzero
#print axioms planeCoordinate_nonzero
#check nonzero_linear_level_null
#print axioms nonzero_linear_level_null
#check plane_coordinate_level_null
#print axioms plane_coordinate_level_null
#check rayOne_absolutelyContinuous
#print axioms rayOne_absolutelyContinuous
#check ray_coordinate_level_null
#print axioms ray_coordinate_level_null
#check ray_coordinate_generic_ae
#print axioms ray_coordinate_generic_ae
#check shifted_plane_level_null
#print axioms shifted_plane_level_null
#check fiberFour_one
#print axioms fiberFour_one
#check fiberFour_two
#print axioms fiberFour_two
#check fiberFour_three
#print axioms fiberFour_three
#check fiber_leg_level_null
#print axioms fiber_leg_level_null
#check fiber_nonoutput_faces_avoided
#print axioms fiber_nonoutput_faces_avoided
#check fiberFour_continuous
#print axioms fiberFour_continuous
#check coordinate_threshold_eventually
#print axioms coordinate_threshold_eventually
#check fiberSharp_continuousWithinAt
#print axioms fiberSharp_continuousWithinAt
#check fiberReadout_base
#print axioms fiberReadout_base
#check fiberReadout_box
#print axioms fiberReadout_box
#check fiberSharp_bound
#print axioms fiberSharp_bound
#check fiberReadout_continuousOn
#print axioms fiberReadout_continuousOn
#check cube_isClosed
#print axioms cube_isClosed
#check cube_isCompact
#print axioms cube_isCompact
#check collisionOutput_congr_on_cube
#print axioms collisionOutput_congr_on_cube
#check collisionIntegrand_continuous
#print axioms collisionIntegrand_continuous
#check collisionOutput_continuousOn
#print axioms collisionOutput_continuousOn
#check continuousExtension_eq
#print axioms continuousExtension_eq
#check collisionMap_apply
#print axioms collisionMap_apply
#check collisionMap_norm_le
#print axioms collisionMap_norm_le
#check triple_difference_bound
#print axioms triple_difference_bound
#check collisionPolynomial_difference_bound
#print axioms collisionPolynomial_difference_bound
#check collisionOutput_difference_bound
#print axioms collisionOutput_difference_bound
#check collisionMap_sub_norm_le
#print axioms collisionMap_sub_norm_le
#check collisionMap_lipschitzOnWith
#print axioms collisionMap_lipschitzOnWith
#check collisionMap_continuous
#print axioms collisionMap_continuous
#check collisionMap_zero
#print axioms collisionMap_zero
#check collisionIntegrand_integrable_continuousOn
#print axioms collisionIntegrand_integrable_continuousOn

end
end Resonance.FiberContinuity
