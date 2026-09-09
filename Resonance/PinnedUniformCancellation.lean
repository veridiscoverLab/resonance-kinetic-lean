import Resonance.PinnedOperator

/-! Uniform C² cancellation for the original complete pinned four-leg
difference. The constants are chosen from the energy geometry before the
test function is quantified. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff ComplexConjugate
namespace Resonance.PinnedUniformCancellation
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedCriticalFactor Resonance.PinnedCriticalNormalization
open Resonance.PinnedCriticalCancellation Resonance.PinnedSurfaceArea
open Resonance.PinnedLocalArea
open Resonance.PinnedFiniteEnergy

theorem squareAverage_bound {f : ℝ→ℝ} {B : ℝ} (hB : ∀x,‖f x‖≤B) (p : Ambient) :
    ‖squareAverage f p‖≤B := by
  letI : IsFiniteMeasure ((volume:Measure (ℝ×ℝ)).restrict unitBox) :=
    ⟨by simpa using (isCompact_Icc:IsCompact unitBox).measure_lt_top (μ:=volume)⟩
  have h := norm_integral_le_of_norm_le_const (μ:=(volume:Measure (ℝ×ℝ)).restrict unitBox)
    (f:=fun q=>f (argumentLinear q p)) (Eventually.of_forall (fun q=>hB _))
  have hset : unitBox=Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
    ext q
    change ((0≤q.1 ∧ 0≤q.2) ∧ (q.1≤1 ∧ q.2≤1)) ↔
      ((0≤q.1 ∧ q.1≤1) ∧ (0≤q.2 ∧ q.2≤1))
    tauto
  have hvol : (volume:Measure (ℝ×ℝ)) unitBox=1 := by
    rw [hset]
    change (volume.prod volume) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)=1
    rw [Measure.prod_prod,Real.volume_Icc]
    norm_num
  simpa [squareAverage,Measure.real,hvol] using h

theorem real_imag_second_derivative {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (x : ℝ) :
    deriv (deriv (fun t=>(φ t).re)) x=(deriv (deriv φ) x).re ∧
    deriv (deriv (fun t=>(φ t).im)) x=(deriv (deriv φ) x).im := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hD (t : ℝ) : HasDerivAt φ (deriv φ t) t :=
    (hφ.differentiable (by norm_num) t).hasDerivAt
  have hD1 (t : ℝ) : HasDerivAt (deriv φ) (deriv (deriv φ) t) t :=
    (h1.differentiable (by norm_num) t).hasDerivAt
  have hR : deriv (fun t=>(φ t).re)=fun t=>(deriv φ t).re :=
    funext (fun t=>(Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hD t)).deriv)
  have hI : deriv (fun t=>(φ t).im)=fun t=>(deriv φ t).im :=
    funext (fun t=>(Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hD t)).deriv)
  rw [hR,hI]
  exact ⟨(Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hD1 x)).deriv,
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hD1 x)).deriv⟩

theorem complexFactor_bound {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) {B : ℝ}
    (hB : ∀x,‖deriv (deriv φ) x‖≤B) (p : Ambient) : ‖complexFactor φ p‖≤2*B := by
  have hR : ‖squareAverage (deriv (deriv (fun t=>(φ t).re))) p‖≤B := by
    apply squareAverage_bound
    intro x
    rw [(real_imag_second_derivative hφ x).1,Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hB x)
  have hI : ‖squareAverage (deriv (deriv (fun t=>(φ t).im))) p‖≤B := by
    apply squareAverage_bound
    intro x
    rw [(real_imag_second_derivative hφ x).2,Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hB x)
  have h := Complex.norm_le_abs_re_add_abs_im (complexFactor φ p)
  change ‖complexFactor φ p‖≤|squareAverage (deriv (deriv (fun t=>(φ t).re))) p|+
    |squareAverage (deriv (deriv (fun t=>(φ t).im))) p| at h
  rw [Real.norm_eq_abs] at hR hI
  linarith

theorem fullDifference_bound {φ : ℝ→ℂ} {B : ℝ} (hB : ∀x,‖φ x‖≤B) (p : Ambient) :
    ‖fullDifference φ p‖≤4*B := by
  unfold fullDifference
  calc
    _ ≤ ‖φ (p 0)+φ (p 1)-φ (p 2)‖+‖φ (p 0+p 1-p 2)‖ := norm_sub_le _ _
    _ ≤ (‖φ (p 0)+φ (p 1)‖+‖φ (p 2)‖)+‖φ (p 0+p 1-p 2)‖ :=
      by linarith [norm_sub_le (φ (p 0)+φ (p 1)) (φ (p 2))]
    _ ≤ ((‖φ (p 0)‖+‖φ (p 1)‖)+‖φ (p 2)‖)+‖φ (p 0+p 1-p 2)‖ :=
      by linarith [norm_add_le (φ (p 0)) (φ (p 1))]
    _ ≤ 4*B := by linarith [hB (p 0),hB (p 1),hB (p 2),hB (p 0+p 1-p 2)]

theorem uniform_gauge_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (swap : Bool) (n m : ℤ) (p : Ambient)
    (hgood : sharedFactor d p≠0 ∨ factorZDerivative d p≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 p, ∀ (φ : ℝ→ℂ) (B : ℝ),
      ContDiff ℝ 2 φ → Function.Periodic φ period → 0≤B →
      (∀x,‖deriv (deriv φ) x‖≤B) → liftedEnergy d (criticalGauge swap n m q)=0 →
      ‖fullDifference φ (criticalGauge swap n m q)‖≤
        C*B*‖energyGradient d (criticalGauge swap n m q)‖ := by
  rcases hgood with hG | hJ
  · refine ⟨0,le_rfl,?_⟩
    filter_upwards [(sharedFactor_contDiff_one hd0 hdU).continuous.continuousAt.eventually_ne hG]
      with q hqG
    intro φ B hφ hp _hB _hD he
    rw [criticalGauge_energy] at he
    have hz := (rectangle_zero_set_decomposition hd0 hdU q).mp he
    rw [fullDifference_gauge hp,complex_rectangle_factor hφ]
    rcases hz with hz | hz | hz
    · simp [hz]
    · simp [hz]
    · exact (hqG hz).elim
  · let a : ℝ := |factorZDerivative d p|/2
    let L : ℝ := ‖gaugeZVector swap‖
    have ha : 0<a := half_pos (abs_pos.mpr hJ)
    have hL : 0≤L := norm_nonneg _
    refine ⟨2*L/a,by positivity,?_⟩
    filter_upwards [(factorZDerivative_continuous hd0 hdU).abs.continuousAt.tendsto.eventually_const_lt
      (half_lt_self (abs_pos.mpr hJ))] with q hq
    intro φ B hφ hp hB hD _
    have hδ : ‖fullDifference φ (criticalGauge swap n m q)‖ ≤ |q 1*q 2| * (2*B) := by
      rw [fullDifference_gauge hp,complex_rectangle_factor hφ,norm_mul]
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg] using
        mul_le_mul_of_nonneg_left (complexFactor_bound hφ hD q) (abs_nonneg (q 1*q 2))
    have hE : a * |q 1*q 2| ≤ L*‖energyGradient d (criticalGauge swap n m q)‖ := by
      calc
        _ ≤ |q 1*q 2| * |factorZDerivative d q| := by
          change a < |factorZDerivative d q| at hq
          nlinarith [abs_nonneg (q 1*q 2)]
        _ ≤ ‖energyGradient d (criticalGauge swap n m q)‖*L :=
          energy_direction_bound hd0 hdU swap n m q
        _ = _ := mul_comm _ _
    have hmul : ‖fullDifference φ (criticalGauge swap n m q)‖*a≤
        2*L*B*‖energyGradient d (criticalGauge swap n m q)‖ := by
      calc
        _ ≤ (|q 1*q 2| * (2*B))*a := mul_le_mul_of_nonneg_right hδ ha.le
        _ = (2*B)*(a * |q 1*q 2|) := by ring
        _ ≤ (2*B)*(L*‖energyGradient d (criticalGauge swap n m q)‖) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by ring
    have he : (2*L/a)*B*‖energyGradient d (criticalGauge swap n m q)‖=
        (2*L*B*‖energyGradient d (criticalGauge swap n m q)‖)/a := by ring
    rw [he]
    exact (le_div_iff₀ ha).mpr hmul

theorem uniform_critical_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 k, ∀ (φ : ℝ→ℂ) (B : ℝ),
      ContDiff ℝ 2 φ → Function.Periodic φ period → 0≤B →
      (∀x,‖deriv (deriv φ) x‖≤B) → liftedEnergy d q=0 →
      ‖fullDifference φ q‖≤C*B*‖energyGradient d q‖ := by
  obtain ⟨swap,n,m,z,v,hk,hgood⟩ :=
    every_critical_point_factor_alternative hd0 hdU he hg
  have hgood' : sharedFactor d (WithLp.toLp 2 ![z,0,v])≠0 ∨
      factorZDerivative d (WithLp.toLp 2 ![z,0,v])≠0 := by
    simpa only [(sharedFactor_z_hasDerivAt hd0 hdU z 0 v).deriv] using hgood
  obtain ⟨C,hC,hnear⟩ := uniform_gauge_gradient_bound hd0 hdU
    swap n m (WithLp.toLp 2 ![z,0,v]) hgood'
  have hT : Tendsto (criticalUngauge swap n m) (𝓝 k) (𝓝 (WithLp.toLp 2 ![z,0,v])) := by
    have h := (criticalUngauge_continuous swap n m).continuousAt (x := k) |>.tendsto
    have hi : criticalUngauge swap n m k=WithLp.toLp 2 ![z,0,v] := by
      rw [←hk,criticalUngauge_gauge]
    rwa [hi] at h
  refine ⟨C,hC,?_⟩
  filter_upwards [hT.eventually hnear] with q hq
  simpa only [criticalGauge_ungauge] using hq

/-- The geometric neighborhood and its constant are independent of the
periodic C² test. Both critical pairings and their windings are included. -/
theorem uniform_local_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (k : Ambient) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 k, ∀ (φ : ℝ→ℂ) (B : ℝ),
      ContDiff ℝ 2 φ → Function.Periodic φ period → 0≤B →
      (∀x,‖φ x‖≤B) → (∀x,‖deriv (deriv φ) x‖≤B) → liftedEnergy d q=0 →
      ‖fullDifference φ q‖≤C*B*‖energyGradient d q‖ := by
  by_cases he : liftedEnergy d k=0
  · by_cases hg : energyGradient d k=0
    · obtain ⟨C,hC,hnear⟩ := uniform_critical_gradient_bound hd0 hdU he hg
      refine ⟨C,hC,?_⟩
      filter_upwards [hnear] with q hq
      exact fun φ B hφ hp hB _h0 h2 hE => hq φ B hφ hp hB h2 hE
    · let a : ℝ := ‖energyGradient d k‖/2
      have ha : 0<a := half_pos (norm_pos_iff.mpr hg)
      refine ⟨4/a,by positivity,?_⟩
      filter_upwards [(energyGradient_continuous hd0 hdU).norm.continuousAt.tendsto.eventually_const_lt
        (half_lt_self (norm_pos_iff.mpr hg))] with q hq
      intro φ B _hφ _hp hB h0 _h2 _hE
      have hqa : a≤‖energyGradient d q‖ := hq.le
      calc
        _ ≤ 4*B := fullDifference_bound h0 q
        _ = (4/a)*B*a := by field_simp
        _ ≤ (4/a)*B*‖energyGradient d q‖ :=
          mul_le_mul_of_nonneg_left hqa (by positivity)
  · refine ⟨0,le_rfl,?_⟩
    filter_upwards [(liftedEnergy_continuous hd0 hdU).continuousAt.eventually_ne he] with q hq
    exact fun _φ _B _hφ _hp _hB _h0 _h2 hE => (hq hE).elim

/-- Compactness is applied once to the original energy geometry. The
resulting constant controls every test in the stated C² ball. -/
theorem uniform_compact_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {K : Set Ambient} (hK : IsCompact K) :
    ∃ C : ℝ, 0≤C ∧ ∀ (φ : ℝ→ℂ) (B : ℝ),
      ContDiff ℝ 2 φ → Function.Periodic φ period → 0≤B →
      (∀x,‖φ x‖≤B) → (∀x,‖deriv (deriv φ) x‖≤B) →
      ∀q∈K, liftedEnergy d q=0 →
      ‖fullDifference φ q‖≤C*B*‖energyGradient d q‖ := by
  classical
  choose C hC hnear using uniform_local_gradient_bound hd0 hdU
  choose r hr hball using fun k=>Metric.mem_nhds_iff.mp (hnear k)
  let U : Ambient→Set Ambient := fun k=>Metric.ball k (r k)
  have hcover : K⊆⋃k,U k := by
    intro k _
    exact mem_iUnion.mpr ⟨k,by simpa [U] using hr k⟩
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover U (fun _=>Metric.isOpen_ball) hcover
  refine ⟨∑j∈J,C j,Finset.sum_nonneg (fun j _=>hC j),?_⟩
  intro φ B hφ hp hB h0 h2 q hq hE
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hJ hq)
  obtain ⟨hjJ,hqj⟩ := mem_iUnion.mp hj
  have hcj : C j≤∑i∈J,C i := Finset.single_le_sum (fun i _=>hC i) hjJ
  have hb := hball j hqj φ B hφ hp hB h0 h2 hE
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcj hB) (norm_nonneg _))

/-- A single complete difference is absolutely integrable. This does not
assert integrability of the uncancelled collision frequency. -/
theorem full_difference_integrableOn {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {K : Set Ambient} (hK : IsCompact K) :
    IntegrableOn (fun k=>‖fullDifference φ k‖) K (liftedRegularCoarea d) := by
  have hreg := regularSurface_measurable hd0 hdU
  have hI := (surfaceRatio_locallyIntegrable hd0 hdU hφ hp).integrableOn_isCompact hK
  have hI' : IntegrableOn (surfaceRatio d φ) K
      ((μH[2] : Measure Ambient).restrict (regularSurface d)) :=
    hI.mono_measure (regular_area_le_zeroSurface d)
  have hJ := hI'.const_mul (((2*Real.pi)^3)⁻¹)
  unfold IntegrableOn liftedRegularCoarea
  rw [restrict_withDensity hK.measurableSet]
  apply (integrable_withDensity_iff (coareaWeight_measurable hd0 hdU)
    (Eventually.of_forall (fun k=>ENNReal.ofReal_lt_top))).mpr
  apply hJ.congr
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem (μ:=μH[2]) hreg)] with k hk
  rw [surfaceRatio,if_pos hk.1,coareaWeight_toReal]
  ring

/-- Uniform bounds on the complete single and squared differences, with
the original regular coarea and one compact real-lift window. -/
theorem uniform_compact_coarea_bounds {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {K : Set Ambient} (hK : IsCompact K) :
    ∃ C : ℝ, 0≤C ∧ ∀ (φ : ℝ→ℂ) (B : ℝ),
      ContDiff ℝ 2 φ → Function.Periodic φ period → 0≤B →
      (∀x,‖φ x‖≤B) → (∀x,‖deriv (deriv φ) x‖≤B) →
      (∫k in K,‖fullDifference φ k‖ ∂liftedRegularCoarea d)≤C*B ∧
      (∫k in K,‖fullDifference φ k‖^2 ∂liftedRegularCoarea d)≤4*C*B^2 := by
  obtain ⟨C,hC,hbound⟩ := uniform_compact_gradient_bound hd0 hdU hK
  let μ : Measure Ambient := ((μH[2] : Measure Ambient).restrict (regularSurface d)).restrict K
  have hμfin : μ Set.univ<(∞:ℝ≥0∞) := by
    change (((μH[2] : Measure Ambient).restrict (regularSurface d)).restrict K) Set.univ<_
    rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,
      Measure.restrict_apply hK.measurableSet]
    exact (measure_mono (by intro x hx;exact ⟨hx.1,hx.2.1⟩)).trans_lt
      (energy_zero_set_compact_finite_area hd0 hdU hK)
  letI : IsFiniteMeasure μ := ⟨hμfin⟩
  let A : ℝ := ((2*Real.pi)^3)⁻¹
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨A*C*μ.real Set.univ,by positivity,?_⟩
  intro φ B hφ hp hB h0 h2
  have hi := full_difference_integrableOn hd0 hdU hφ hp hK
  have hi2 := full_difference_square_integrableOn hd0 hdU hφ hp hK
  have hreg := regularSurface_measurable hd0 hdU
  have hdens : ∀ᵐ k ∂μ, (coareaWeight d k).toReal*‖fullDifference φ k‖≤A*C*B := by
    filter_upwards [ae_restrict_mem (μ:=(μH[2] : Measure Ambient).restrict (regularSurface d))
      hK.measurableSet,ae_restrict_of_ae (ae_restrict_mem (μ:=μH[2]) hreg)] with k hk hkr
    have hb := hbound φ B hφ hp hB h0 h2 k hk hkr.1
    have hn : 0<‖energyGradient d k‖ := norm_pos_iff.mpr hkr.2
    have hdiv := (div_le_iff₀ hn).mpr hb
    rw [coareaWeight_toReal]
    calc
      _ = A*(‖fullDifference φ k‖/‖energyGradient d k‖) := by dsimp [A]; ring
      _ ≤ A*(C*B) := mul_le_mul_of_nonneg_left hdiv hA
      _ = _ := by ring
  have hdI : Integrable (fun k=>(coareaWeight d k).toReal*‖fullDifference φ k‖) μ := by
    unfold IntegrableOn liftedRegularCoarea at hi
    rw [restrict_withDensity hK.measurableSet] at hi
    simpa only [smul_eq_mul,mul_comm] using
      (integrable_withDensity_iff (coareaWeight_measurable hd0 hdU)
        (Eventually.of_forall (fun k=>ENNReal.ofReal_lt_top))).mp hi
  have hlinear : (∫k in K,‖fullDifference φ k‖ ∂liftedRegularCoarea d)≤
      A*C*μ.real Set.univ*B := by
    unfold liftedRegularCoarea
    rw [restrict_withDensity hK.measurableSet,
      integral_withDensity_eq_integral_toReal_smul (coareaWeight_measurable hd0 hdU)
        (Eventually.of_forall (fun k=>ENNReal.ofReal_lt_top))]
    change (∫k,(coareaWeight d k).toReal*‖fullDifference φ k‖ ∂μ)≤_
    calc
      _ ≤ ∫_k,A*C*B ∂μ := integral_mono_ae hdI (integrable_const _) hdens
      _ = _ := by rw [integral_const]; simp only [smul_eq_mul]; ring
  refine ⟨hlinear,?_⟩
  calc
    _ ≤ ∫k in K,(4*B)*‖fullDifference φ k‖ ∂liftedRegularCoarea d := by
      apply integral_mono_ae hi2 (hi.const_mul (4*B))
      exact Eventually.of_forall (fun k=>by
        have h := fullDifference_bound h0 k
        nlinarith [norm_nonneg (fullDifference φ k)])
    _ = (4*B)*(∫k in K,‖fullDifference φ k‖ ∂liftedRegularCoarea d) := integral_const_mul _ _
    _ ≤ (4*B)*(A*C*μ.real Set.univ*B) := mul_le_mul_of_nonneg_left hlinear (by positivity)
    _ = _ := by ring

theorem periodic_deriv {φ : ℝ→ℂ} (hp : Function.Periodic φ period) :
    Function.Periodic (deriv φ) period := by
  intro x
  rw [←deriv_comp_add_const]
  have he : (fun t=>φ (t+period))=φ := funext hp
  rw [he]

/-- The ordinary sum-of-suprema C² norm of the periodic lift. Its three
suprema are proved finite for every periodic C² test below. -/
def c2Norm (φ : ℝ→ℂ) : ℝ :=
  sSup (Set.range (fun x=>‖φ x‖))+
  sSup (Set.range (fun x=>‖deriv φ x‖))+
  sSup (Set.range (fun x=>‖deriv (deriv φ) x‖))

theorem periodic_norm_range_compact {φ : ℝ→ℂ} (hc : Continuous φ)
    (hp : Function.Periodic φ period) : IsCompact (Set.range (fun x=>‖φ x‖)) := by
  have hn : Function.Periodic (fun x=>‖φ x‖) period := fun x=>congrArg norm (hp x)
  exact hn.compact_of_continuous period_pos.ne' hc.norm

theorem c2Norm_bounds {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ)
    (hp : Function.Periodic φ period) :
    0≤c2Norm φ ∧ (∀x,‖φ x‖≤c2Norm φ) ∧ (∀x,‖deriv (deriv φ) x‖≤c2Norm φ) := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have h2 : ContDiff ℝ 0 (deriv (deriv φ)) := h1.deriv'
  have b0 := (periodic_norm_range_compact hφ.continuous hp).bddAbove
  have b1 := (periodic_norm_range_compact h1.continuous (periodic_deriv hp)).bddAbove
  have b2 := (periodic_norm_range_compact h2.continuous (periodic_deriv (periodic_deriv hp))).bddAbove
  have l0 (x : ℝ) : ‖φ x‖ ≤ sSup (Set.range (fun t=>‖φ t‖)) := le_csSup b0 ⟨x,rfl⟩
  have l1 (x : ℝ) : ‖deriv φ x‖ ≤ sSup (Set.range (fun t=>‖deriv φ t‖)) := le_csSup b1 ⟨x,rfl⟩
  have l2 (x : ℝ) : ‖deriv (deriv φ) x‖ ≤ sSup (Set.range (fun t=>‖deriv (deriv φ) t‖)) :=
    le_csSup b2 ⟨x,rfl⟩
  have p0 := (norm_nonneg (φ 0)).trans (l0 0)
  have p1 := (norm_nonneg (deriv φ 0)).trans (l1 0)
  have p2 := (norm_nonneg (deriv (deriv φ) 0)).trans (l2 0)
  dsimp [c2Norm]
  exact ⟨by positivity,fun x=>by linarith [l0 x],fun x=>by linarith [l2 x]⟩

theorem compact_c2_coarea_estimates {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {K : Set Ambient} (hK : IsCompact K) :
    ∃ C : ℝ, 0≤C ∧ ∀ (φ : ℝ→ℂ),
      ContDiff ℝ 2 φ → Function.Periodic φ period →
      (∫k in K,‖fullDifference φ k‖ ∂liftedRegularCoarea d)≤C*c2Norm φ ∧
      (∫k in K,‖fullDifference φ k‖^2 ∂liftedRegularCoarea d)≤4*C*(c2Norm φ)^2 := by
  obtain ⟨C,hC,hall⟩ := uniform_compact_coarea_bounds hd0 hdU hK
  refine ⟨C,hC,?_⟩
  intro φ hφ hp
  obtain ⟨hB,h0,h2⟩ := c2Norm_bounds hφ hp
  exact hall φ (c2Norm φ) hφ hp hB h0 h2

end
end Resonance.PinnedUniformCancellation
