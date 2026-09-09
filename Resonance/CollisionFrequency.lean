import Resonance.FiberContinuity

/-! The loss frequency is defined directly on the same physical sharp-cube
collision fibers.  In particular corner vanishing is a pointwise statement
about the entire actual fiber measure, not an almost-everywhere choice of
a marginal density.  No replacement positive frequency is introduced. -/
open Real MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal EuclideanGeometry ProbabilityTheory
namespace Resonance.CollisionFrequency
noncomputable section
open Resonance.PlaneCoarea Resonance.PlaneGlobal Resonance.CollisionFiber
open Resonance.FiberContinuity

def isCubeCorner (R:ℝ) (k:E) : Prop := ∀j:Fin 3,|k j|=R

theorem corner_coordinate_product_nonneg {R k x y:ℝ}
    (hk:|k|=R) (hx:|k+x|≤R) (hy:|k+y|≤R) : 0≤x*y := by
  rcases le_total 0 k with hp | hn
  · rw [abs_of_nonneg hp] at hk
    have hx' : x≤0 := by linarith [(abs_le.mp hx).2]
    have hy' : y≤0 := by linarith [(abs_le.mp hy).2]
    exact mul_nonneg_of_nonpos_of_nonpos hx' hy'
  · rw [abs_of_nonpos hn] at hk
    have hx' : 0≤x := by linarith [(abs_le.mp hx).1]
    have hy' : 0≤y := by linarith [(abs_le.mp hy).1]
    exact mul_nonneg hx' hy'

/-- On a corner fiber every allowed orthogonal rectangle has a moving
leg on an original cube face.  All original flags remain in the premise. -/
theorem corner_rectangle_moving_face {R:ℝ} {k x y:E}
    (hk:isCubeCorner R k)
    (hflags:rectangleFour k x y∈CoareaNormalization.allFourFlags R)
    (horth:inner ℝ x y=0) :
    ∃i:Fin 4,i≠0 ∧ |rectangleFour k x y i 0|=R := by
  have hprod (j:Fin 3) : 0≤x j*y j :=
    corner_coordinate_product_nonneg (hk j) (hflags 2 j) (hflags 3 j)
  have hsum : x 0*y 0+(x 1*y 1+x 2*y 2)=0 := by
    simpa only [PiLp.inner_apply,real_inner_apply,Fin.sum_univ_succ,
      Fin.sum_univ_zero,add_zero,mul_comm] using horth
  have h0 : x 0*y 0=0 := by linarith [hprod 0,hprod 1,hprod 2]
  rcases mul_eq_zero.mp h0 with hx | hy
  · refine ⟨2,by decide,?_⟩
    simpa [rectangleFour,hx] using hk 0
  · refine ⟨3,by decide,?_⟩
    simpa [rectangleFour,hy] using hk 0

theorem fiberFour_rectangle (k:E) (b:FiberParameters) :
    fiberFour k b=rectangleFour k (PolarCoordinates.polarVector b.1)
      (planePoint b.1.1 b.2) := by
  simp [fiberFour,planeShell,PolarCoordinates.polarVector,normalCoords_zero,planePoint]

theorem fiber_rectangle_orthogonal (b:FiberParameters) :
    inner ℝ (PolarCoordinates.polarVector b.1) (planePoint b.1.1 b.2)=0 := by
  simp only [PolarCoordinates.polarVector,planePoint_eq,real_inner_smul_left,
    planeIsometry_inner_normal,mul_zero]

/-- The complete actual physical fiber is zero at every one of the eight
corners, pointwise in the output momentum. -/
theorem fiberMeasure_corner_zero {R:ℝ} {k:E} (hk:isCubeCorner R k) :
    fiberMeasure R k=0 := by
  have ha : ∀ᵐb∂fiberBase,b∉fiberAllowed R k := by
    filter_upwards [fiber_nonoutput_faces_avoided k R] with b hb
    intro hf
    have hf' : rectangleFour k (PolarCoordinates.polarVector b.1)
        (planePoint b.1.1 b.2)∈CoareaNormalization.allFourFlags R := by
      rw [←fiberFour_rectangle k b]
      exact hf
    obtain ⟨i,hi,hface⟩ := corner_rectangle_moving_face hk hf' (fiber_rectangle_orthogonal b)
    rw [←fiberFour_rectangle k b] at hface
    exact hb i hi 0 hface
  have hz : fiberBase (fiberAllowed R k)=0 := by
    simpa only [ae_iff,not_not] using ha
  simp [fiberMeasure,Measure.restrict_eq_zero.mpr hz]

def geometricFrequency (R:ℝ) (k:E) : ℝ := fiberReadout R (fun _=>1) k

def lossFrequency (R:ℝ) (N:E→ℝ) (k:E) : ℝ :=
  (N k)⁻¹ * fiberReadout R (fun q => N (q 1) * N (q 2) * N (q 3)) k

def referenceProfile (k:E) : ℝ := (1+‖k‖^2)⁻¹

/-- The paper's fixed `nu_*`, with the literal reference `(1+|k|²)^(-1)`. -/
def referenceFrequency (R:ℝ) : E→ℝ := lossFrequency R referenceProfile

theorem geometricFrequency_mass_finite {R:ℝ} (hR:0≤R) (k:E) :
    fiberMeasure R k univ<∞ :=
  lt_of_le_of_lt (fiberMeasure_mass_le hR k) (fiberMassBound_lt_top R)

theorem geometricFrequency_eq_mass (R:ℝ) (k:E) :
    geometricFrequency R k=(fiberMeasure R k univ).toReal := by
  simp [geometricFrequency,fiberReadout,integral_const,measureReal_def]

theorem geometricFrequency_nonnegative (R:ℝ) (k:E) :
    0≤geometricFrequency R k := by
  rw [geometricFrequency_eq_mass R]
  exact ENNReal.toReal_nonneg

theorem geometricFrequency_continuousOn {R:ℝ} (hR:0≤R) :
    ContinuousOn (geometricFrequency R) (ResonantMeasure.cube R) :=
  fiberReadout_continuousOn hR (fun _=>1) continuous_const

theorem lossFrequency_continuousOn {R:ℝ} (hR:0≤R) {N:E→ℝ}
    (hN:Continuous N) (hpos:∀k∈ResonantMeasure.cube R,0<N k) :
    ContinuousOn (lossFrequency R N) (ResonantMeasure.cube R) := by
  unfold lossFrequency
  apply ContinuousOn.mul
  · exact hN.continuousOn.inv₀ (fun k hk=>(hpos k hk).ne')
  · apply fiberReadout_continuousOn hR
    fun_prop

theorem referenceProfile_continuous : Continuous referenceProfile := by
  apply Continuous.inv₀ (by fun_prop)
  intro k
  exact ne_of_gt (by positivity : 0<1+‖k‖^2)

theorem referenceProfile_positive (k:E) : 0<referenceProfile k := by
  unfold referenceProfile
  positivity

theorem referenceFrequency_continuousOn {R:ℝ} (hR:0≤R) :
    ContinuousOn (referenceFrequency R) (ResonantMeasure.cube R) :=
  lossFrequency_continuousOn hR referenceProfile_continuous (fun k _=>referenceProfile_positive k)

theorem geometricFrequency_corner_zero {R:ℝ} {k:E} (hk:isCubeCorner R k) :
    geometricFrequency R k=0 := by
  simp [geometricFrequency,fiberReadout,fiberMeasure_corner_zero hk]

theorem lossFrequency_corner_zero {R:ℝ} {k:E} (hk:isCubeCorner R k) (N:E→ℝ) :
    lossFrequency R N k=0 := by
  simp [lossFrequency,fiberReadout,fiberMeasure_corner_zero hk]

theorem referenceFrequency_corner_zero {R:ℝ} {k:E} (hk:isCubeCorner R k) :
    referenceFrequency R k=0 := lossFrequency_corner_zero hk referenceProfile

/-- Pointwise comparison with the actual geometric fiber mass.  Both
integrals are proved finite before monotonicity is used. -/
theorem lossFrequency_geometric_bounds {R m M : ℝ} (hR : 0 ≤ R) (hm : 0 < m) (hM : 0 < M)
    (N : E → ℝ) (hN : Measurable N)
    (hb : ∀p∈ResonantMeasure.cube R, m ≤ N p ∧ N p ≤ M)
    {k:E} (hk:k∈ResonantMeasure.cube R) :
    (m^3/M)*geometricFrequency R k≤lossFrequency R N k ∧
      lossFrequency R N k≤(M^3/m)*geometricFrequency R k := by
  let μ := fiberMeasure R k
  letI : IsFiniteMeasure μ := ⟨geometricFrequency_mass_finite hR k⟩
  let Φ : FourMomenta→ℝ := fun q=>N (q 1)*N (q 2)*N (q 3)
  have hΦm : Measurable Φ := by dsimp [Φ]; fun_prop
  have hΦbounds : ∀ᵐq∂μ,m^3≤Φ q ∧ Φ q≤M^3 := by
    filter_upwards [fiber_support R k] with q hq
    have h1 := hb (q 1) (hq.1 1)
    have h2 := hb (q 2) (hq.1 2)
    have h3 := hb (q 3) (hq.1 3)
    have hp1 := hm.le.trans h1.1
    have hp2 := hm.le.trans h2.1
    have hp3 := hm.le.trans h3.1
    constructor
    · calc
        m^3=m*m*m := by ring
        _ ≤ Φ q := mul_le_mul (mul_le_mul h1.1 h2.1 hm.le hp1) h3.1 hm.le
          (mul_nonneg hp1 hp2)
    · calc
        Φ q ≤ M*M*M := mul_le_mul (mul_le_mul h1.2 h2.2 hp2 hM.le) h3.2 hp3
          (mul_nonneg hM.le hM.le)
        _ = M^3 := by ring
  have hΦi : Integrable Φ μ := by
    apply (integrable_const (M^3)).mono' hΦm.aestronglyMeasurable
    filter_upwards [hΦbounds] with q hq
    rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by positivity) hq.1)]
    exact hq.2
  have hconst (t:ℝ) : (∫q,t∂μ)=t*geometricFrequency R k := by
    simp [μ,geometricFrequency,fiberReadout,integral_const,mul_comm]
  have hlo : m^3*geometricFrequency R k≤∫q,Φ q∂μ := by
    rw [←hconst]
    exact integral_mono_ae (integrable_const _) hΦi (hΦbounds.mono (fun _ h=>h.1))
  have hhi : (∫q,Φ q∂μ)≤M^3*geometricFrequency R k := by
    rw [←hconst]
    exact integral_mono_ae hΦi (integrable_const _) (hΦbounds.mono (fun _ h=>h.2))
  have hNk := hb k hk
  have hNkpos := lt_of_lt_of_le hm hNk.1
  have hinvlo : 1/M≤(N k)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hNkpos hNk.2
  have hinvhi : (N k)⁻¹≤1/m := by
    simpa only [one_div] using one_div_le_one_div_of_le hm hNk.1
  have hmass := geometricFrequency_nonnegative R k
  have hi0 : 0≤∫q,Φ q∂μ := (mul_nonneg (by positivity) hmass).trans hlo
  constructor
  · calc
      (m^3/M)*geometricFrequency R k=(1/M)*(m^3*geometricFrequency R k) := by ring
      _ ≤ (N k)⁻¹*(∫q,Φ q∂μ) := mul_le_mul hinvlo hlo (by positivity) (inv_nonneg.mpr hNkpos.le)
      _ = lossFrequency R N k := rfl
  · calc
      lossFrequency R N k=(N k)⁻¹*(∫q,Φ q∂μ) := rfl
      _ ≤ (1/m)*(M^3*geometricFrequency R k) := mul_le_mul hinvhi hhi hi0 (by positivity)
      _ = (M^3/m)*geometricFrequency R k := by ring

theorem referenceProfile_bounds {R:ℝ} (hR:0≤R) {k:E} (hk:k∈ResonantMeasure.cube R) :
    (1+9*R^2)⁻¹≤referenceProfile k ∧ referenceProfile k≤1 := by
  have hn := ResonantMeasure.norm_le_three_R hR hk
  have hsq : ‖k‖^2≤9*R^2 := by nlinarith [norm_nonneg k]
  constructor
  · have h : 1/(1+9*R^2)≤1/(1+‖k‖^2) :=
      one_div_le_one_div_of_le (by positivity : 0<1+‖k‖^2)
        (by linarith : 1+‖k‖^2≤1+9*R^2)
    simpa only [referenceProfile,one_div] using h
  · have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
      (le_add_of_nonneg_right (sq_nonneg ‖k‖))
    simpa [referenceProfile,one_div] using h

theorem referenceFrequency_geometric_bounds {R:ℝ} (hR:0≤R)
    {k:E} (hk:k∈ResonantMeasure.cube R) :
    ((1+9*R^2)⁻¹)^3*geometricFrequency R k≤referenceFrequency R k ∧
      referenceFrequency R k≤(1+9*R^2)*geometricFrequency R k := by
  have h := lossFrequency_geometric_bounds hR
    (by positivity : 0<(1+9*R^2)⁻¹) (by norm_num : (0:ℝ)<1)
    referenceProfile referenceProfile_continuous.measurable
    (fun p hp=>referenceProfile_bounds hR hp) hk
  simpa [referenceFrequency,div_eq_mul_inv] using h

end
end Resonance.CollisionFrequency
