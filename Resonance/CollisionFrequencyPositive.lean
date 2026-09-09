import Resonance.CollisionFrequency

/-! Strict positivity away from the eight original cube corners is
obtained from actual open subsets of the same sharp physical fiber. -/
open Real MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal EuclideanGeometry ProbabilityTheory Topology
namespace Resonance.CollisionFrequencyPositive
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea Resonance.PlaneGlobal Resonance.CollisionFiber
open Resonance.FiberContinuity Resonance.CollisionFrequency

def inwardSign (t:ℝ) : ℝ := if 0≤t then -1 else 1

theorem inwardSign_sq (t:ℝ) : inwardSign t^2=1 := by
  unfold inwardSign
  split <;> norm_num

theorem inwardSign_nonzero (t:ℝ) : inwardSign t≠0 := by
  unfold inwardSign
  split <;> norm_num

theorem inward_strict {R t s:ℝ} (ht:|t|≤R) (hs:0<s) (hsR:s<R) :
    |t+inwardSign t*s|<R := by
  rw [abs_lt]
  unfold inwardSign
  split_ifs with h
  · have hab := abs_le.mp ht
    constructor <;> linarith
  · have hab := abs_le.mp ht
    have hn : t<0 := lt_of_not_ge h
    constructor <;> linarith

def witnessX (k:E) (j:Fin 3) (s:ℝ) : E :=
  WithLp.toLp 2 (fun i=>if i=j then 2*s else inwardSign (k i)*s)

def witnessY (k:E) (j:Fin 3) (s:ℝ) : E :=
  WithLp.toLp 2 (fun i=>if i=j then -s else inwardSign (k i)*s)

theorem witness_inner (k:E) (j:Fin 3) (s:ℝ) :
    inner ℝ (witnessX k j s) (witnessY k j s)=0 := by
  have hm (i:Fin 3) : witnessY k j s i*witnessX k j s i=
      if i=j then -2*s^2 else s^2 := by
    by_cases hi:i=j
    · simp [witnessX,witnessY,hi]
      ring
    · simp only [witnessX,witnessY,WithLp.ofLp_toLp,if_neg hi]
      calc
        inwardSign (k i)*s*(inwardSign (k i)*s)=(inwardSign (k i))^2*s^2 := by ring
        _ = s^2 := by rw [inwardSign_sq,one_mul]
  rw [PiLp.inner_apply]
  simp only [real_inner_apply]
  rw [Finset.sum_congr rfl (fun i _=>hm i)]
  fin_cases j <;> simp [Fin.sum_univ_succ] <;> ring

theorem witnessX_coordinate_nonzero (k:E) (j i:Fin 3) {s:ℝ} (hs:0<s) :
    witnessX k j s i≠0 := by
  by_cases hi:i=j
  · simp [witnessX,hi,hs.ne']
  · simpa [witnessX,hi] using mul_ne_zero (inwardSign_nonzero (k i)) hs.ne'

theorem witness_moving_strict {R:ℝ} {k:E}
    (hk:k∈ResonantMeasure.cube R) (j:Fin 3) {s:ℝ}
    (hs:0<s) (hsR:2*s<R) (hsj:|k j|+2*s<R) :
    ∀i:Fin 4,i≠0→∀l:Fin 3,
      |rectangleFour k (witnessX k j s) (witnessY k j s) i l|<R := by
  have hsR' : s<R := by linarith
  have htwo : 0<2*s := by positivity
  intro i hi l
  by_cases hlj:l=j
  · subst l
    fin_cases i
    · exact (hi rfl).elim
    · have h : |k j+s|<R :=
        (abs_add_le (k j) s).trans_lt (by rw [abs_of_pos hs]; linarith)
      simp [rectangleFour, witnessX, witnessY]
      convert h using 1
      congr 1
      ring
    · have h : |k j+2*s|<R :=
        (abs_add_le (k j) (2*s)).trans_lt (by rw [abs_of_pos htwo]; exact hsj)
      simpa [rectangleFour,witnessX,witnessY] using h
    · have h : |k j+(-s)|<R :=
        (abs_add_le (k j) (-s)).trans_lt (by rw [abs_neg,abs_of_pos hs]; linarith)
      simpa [rectangleFour,witnessX,witnessY] using h
  · fin_cases i
    · exact (hi rfl).elim
    · have h := inward_strict (hk l) htwo hsR
      change |k l+(if l=j then 2*s else inwardSign (k l)*s)+
        (if l=j then -s else inwardSign (k l)*s)|<R
      simp only [if_neg hlj]
      convert h using 1
      congr 1
      ring
    · simpa [rectangleFour,witnessX,witnessY,hlj] using inward_strict (hk l) hs hsR'
    · simpa [rectangleFour,witnessX,witnessY,hlj] using inward_strict (hk l) hs hsR'

/-- A real orthogonal rectangle with all moving legs strictly inside the
cube exists at every noncorner output, including face and edge outputs. -/
theorem noncorner_rectangle_witness {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) (hn:¬isCubeCorner R k) :
    ∃x y:E,inner ℝ x y=0 ∧ x 1≠0 ∧
      ∀i:Fin 4,i≠0→∀l:Fin 3,|rectangleFour k x y i l|<R := by
  have hj : ∃j:Fin 3,|k j|<R := by
    by_contra h
    push Not at h
    exact hn (fun j=>le_antisymm (hk j) (h j))
  obtain ⟨j,hj⟩ := hj
  have hb : 0 < min ((R-|k j|)/4) (R/4) :=
    lt_min (by linarith) (by linarith)
  obtain ⟨s,hs,hsb⟩ := exists_between hb
  have hs1 := (lt_min_iff.mp hsb).1
  have hs2 := (lt_min_iff.mp hsb).2
  refine ⟨witnessX k j s,witnessY k j s,witness_inner k j s,
    witnessX_coordinate_nonzero k j 1 hs,?_⟩
  exact witness_moving_strict hk j hs (by linarith) (by linarith)

theorem radialOne_open_positive : radialOne.IsOpenPosMeasure := by
  let μ : Measure Radius := (volume : Measure ℝ).comap Subtype.val
  letI : μ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap volume
    isOpen_Ioi.isOpenEmbedding_subtypeVal
  have hac : μ ≪ radialOne := by
    apply withDensity_absolutelyContinuous'
    · exact (by fun_prop : Measurable (fun r : Radius =>
        ENNReal.ofReal ((r:ℝ)^1))).aemeasurable
    · exact Filter.Eventually.of_forall (fun r=>by
        simp only [pow_one, ne_eq, ENNReal.ofReal_eq_zero]
        exact not_le.mpr r.property)
  exact hac.isOpenPosMeasure

theorem fiberBase_open_positive : fiberBase.IsOpenPosMeasure := by
  letI := radialOne_open_positive
  unfold fiberBase rayOne ResonantMeasure.surface
  infer_instance

theorem householder_continuousAt (σ : Sphere) (y : E) (hσ : (σ:E)≠e0) :
    ContinuousAt (fun p : Sphere×E=>householder p.1 p.2) (σ,y) := by
  have hn : ‖e0-(σ:E)‖^2≠0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hσ.symm))
  simp_rw [householder_explicit]
  have hv : ContinuousAt (fun p : Sphere×E => (p.1:E)) (σ,y) :=
    continuous_subtype_val.continuousAt.comp continuousAt_fst
  have hd : ContinuousAt (fun p : Sphere×E=>e0-(p.1:E)) (σ,y) :=
    continuousAt_const.sub hv
  exact continuousAt_snd.sub ((continuousAt_const.mul
    ((hd.inner continuousAt_snd).div (hd.norm.pow 2) hn)).smul hd)

theorem planePoint_continuousAt (σ : Sphere) (z : E2) (hσ : (σ:E)≠e0) :
    ContinuousAt (fun p : Sphere×E2=>planePoint p.1 p.2) (σ,z) := by
  have hh := householder_continuousAt σ (flatEmbedding z) hσ
  exact hh.comp (f:=fun p : Sphere×E2=>(p.1,flatIsometry p.2))
    (by fun_prop : ContinuousAt
      (fun p : Sphere×E2=>(p.1,flatIsometry p.2)) (σ,z))

theorem fiberFour_parameters_continuousAt (k:E) (b:FiberParameters)
    (hb : (b.1.1:E)≠e0) : ContinuousAt (fiberFour k) b := by
  apply continuousAt_pi.mpr
  intro i
  have hp : ContinuousAt (fun b:FiberParameters=>planePoint b.1.1 b.2) b :=
    (planePoint_continuousAt b.1.1 b.2 hb).comp
      (f:=fun b:FiberParameters=>(b.1.1,b.2)) (by fun_prop)
  have hr : ContinuousAt (fun b:FiberParameters=>PolarCoordinates.polarVector b.1) b := by
    unfold PolarCoordinates.polarVector
    fun_prop
  have hkC : ContinuousAt (fun _:FiberParameters=>k) b := continuousAt_const
  fin_cases i
  · simpa using hkC
  · change ContinuousAt (fun y=>fiberFour k y 1) b
    simp_rw [fiberFour_one]
    exact (hkC.add hr).add hp
  · simpa only [fiberFour_two] using hkC.add hr
  · change ContinuousAt (fun y=>fiberFour k y 3) b
    simp_rw [fiberFour_three]
    exact hkC.add hp

theorem rectangle_in_fiber_parameters {k x y:E}
    (hx:x 1≠0) (hxy:inner ℝ x y=0) :
    ∃b:FiberParameters,(b.1.1:E)≠e0 ∧
      fiberFour k b=rectangleFour k x y := by
  have hx0 : x≠0 := by
    intro h
    exact hx (by simp [h])
  have hnx : 0<‖x‖ := norm_pos_iff.mpr hx0
  let σ : Sphere := ⟨‖x‖⁻¹ • x,by
    rw [mem_sphere_zero_iff_norm]
    simp [norm_smul,hnx.ne']⟩
  let r : Radius := ⟨‖x‖,hnx⟩
  have hr : (r:ℝ) • (σ:E)=x := by
    simp [r,σ,smul_smul,hnx.ne']
  have hσ : (σ:E)≠e0 := by
    intro h
    have h1 := congrArg (fun z:E=>z 1) h
    have hv : (‖x‖⁻¹:ℝ)*x 1=0 := by
      simpa [σ,e0] using h1
    exact (mul_ne_zero (inv_ne_zero hnx.ne') hx) hv
  have hy : y∈normalPlane σ := by
    change inner ℝ (‖x‖⁻¹ • x) y=0
    simp [real_inner_smul_left,hxy]
  rw [←plane_range σ] at hy
  obtain ⟨z,hz⟩ := hy
  refine ⟨((σ,r),z),hσ,?_⟩
  rw [fiberFour_rectangle]
  have hp : planePoint σ z=y := by simpa only [planePoint_eq] using hz
  simp only [PolarCoordinates.polarVector,hr,hp]

theorem strict_fiber_mem_nhds {R:ℝ} {k:E}
    (hk:k∈ResonantMeasure.cube R) {b:FiberParameters}
    (hb:(b.1.1:E)≠e0)
    (hm:∀i:Fin 4,i≠0→∀j:Fin 3,|fiberFour k b i j|<R) :
    fiberAllowed R k∈𝓝 b := by
  have hc := fiberFour_parameters_continuousAt k b hb
  have he : ∀ᶠ b' in 𝓝 b,∀i:Fin 4,i≠0→∀j:Fin 3,
      |fiberFour k b' i j|<R := by
    simp only [Filter.eventually_all]
    intro i hi j
    have hiC := (continuous_apply i).continuousAt.comp hc
    have hjC := (EuclideanSpace.proj j).continuous.continuousAt.comp hiC
    exact hjC.abs.eventually (isOpen_Iio.mem_nhds (hm i hi j))
  filter_upwards [he] with b' hb'
  intro i
  by_cases hi:i=0
  · simpa [hi,fiberFour_output] using hk
  · exact fun j=>(hb' i hi j).le

theorem fiberMeasure_noncorner_positive {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) (hn:¬isCubeCorner R k) :
    0<fiberMeasure R k univ := by
  obtain ⟨x,y,hxy,hx,hm⟩ := noncorner_rectangle_witness hR hk hn
  obtain ⟨b,hb,hbf⟩ := rectangle_in_fiber_parameters (k:=k) hx hxy
  have hm' : ∀i:Fin 4,i≠0→∀j:Fin 3,|fiberFour k b i j|<R := by
    simpa only [hbf] using hm
  have hnB := strict_fiber_mem_nhds hk hb hm'
  letI := fiberBase_open_positive
  have hpos : 0<fiberBase (fiberAllowed R k) :=
    MeasureTheory.Measure.measure_pos_of_mem_nhds fiberBase hnB
  rw [fiberMeasure_apply R k MeasurableSet.univ]
  simpa only [mem_univ,true_and] using
    ENNReal.mul_pos (by norm_num : (1/2:ℝ≥0∞)≠0) hpos.ne'

theorem geometricFrequency_noncorner_positive {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) (hn:¬isCubeCorner R k) :
    0<geometricFrequency R k := by
  rw [geometricFrequency_eq_mass]
  exact ENNReal.toReal_pos (ne_of_gt (fiberMeasure_noncorner_positive hR hk hn))
    (geometricFrequency_mass_finite hR.le k).ne

theorem referenceFrequency_noncorner_positive {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) (hn:¬isCubeCorner R k) :
    0<referenceFrequency R k := by
  have hm := geometricFrequency_noncorner_positive hR hk hn
  exact lt_of_lt_of_le (mul_pos (by positivity) hm)
    (referenceFrequency_geometric_bounds hR.le hk).1

theorem geometricFrequency_eq_zero_iff {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) :
    geometricFrequency R k=0 ↔ isCubeCorner R k := by
  refine ⟨fun hz=>?_,geometricFrequency_corner_zero⟩
  by_contra hn
  have h := geometricFrequency_noncorner_positive hR hk hn
  exact h.ne' hz

theorem referenceFrequency_eq_zero_iff {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) :
    referenceFrequency R k=0 ↔ isCubeCorner R k := by
  refine ⟨fun hz=>?_,referenceFrequency_corner_zero⟩
  by_contra hn
  have h := referenceFrequency_noncorner_positive hR hk hn
  exact h.ne' hz

theorem lossFrequency_eq_zero_iff {R m M:ℝ} (hR:0<R)
    (hm : 0 < m) (hM : 0 < M) (N:E→ℝ) (hN:Measurable N)
    (hb:∀p∈ResonantMeasure.cube R,m≤N p ∧ N p≤M)
    {k:E} (hk:k∈ResonantMeasure.cube R) :
    lossFrequency R N k=0 ↔ isCubeCorner R k := by
  refine ⟨fun hz=>?_,fun h=>lossFrequency_corner_zero h N⟩
  by_contra hn
  have hg := geometricFrequency_noncorner_positive hR hk hn
  have hpos : 0<lossFrequency R N k := lt_of_lt_of_le
    (mul_pos (by positivity) hg)
    (lossFrequency_geometric_bounds hR.le hm hM N hN hb hk).1
  exact hpos.ne' hz

end
end Resonance.CollisionFrequencyPositive
