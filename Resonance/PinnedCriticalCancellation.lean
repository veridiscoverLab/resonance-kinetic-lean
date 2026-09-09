import Resonance.PinnedSurfaceArea

/-! The full complex four-leg difference shares the energy factor. The
directional energy estimate is in the original Euclidean momentum metric. -/
open Real Set MeasureTheory Filter
open scoped Topology ContDiff ComplexConjugate
namespace Resonance.PinnedCriticalCancellation
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedCriticalFactor Resonance.PinnedCriticalNormalization
open Resonance.PinnedSurfaceArea Resonance.PinnedLocalArea Resonance.PinnedLegAC

def fullDifference (φ : ℝ→ℂ) (k : Ambient) : ℂ :=
  φ (k 0)+φ (k 1)-φ (k 2)-φ (k 0+k 1-k 2)

def complexFactor (φ : ℝ→ℂ) (p : Ambient) : ℂ :=
  ⟨squareAverage (deriv (deriv (fun t => (φ t).re))) p,
    squareAverage (deriv (deriv (fun t => (φ t).im))) p⟩

theorem complexFactor_continuous {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (complexFactor φ) := by
  have hR : ContDiff ℝ 2 (fun t => (φ t).re) := Complex.reCLM.contDiff.comp hφ
  have hI : ContDiff ℝ 2 (fun t => (φ t).im) := Complex.imCLM.contDiff.comp hφ
  have hR1 : ContDiff ℝ 1 (deriv (fun t => (φ t).re)) := hR.deriv'
  have hI1 : ContDiff ℝ 1 (deriv (fun t => (φ t).im)) := hI.deriv'
  have hRc := squareAverage_continuous (hR1.continuous_deriv (by norm_num))
  have hIc := squareAverage_continuous (hI1.continuous_deriv (by norm_num))
  have he : complexFactor φ=fun p =>
      (squareAverage (deriv (deriv (fun t => (φ t).re))) p : ℂ)+
      (squareAverage (deriv (deriv (fun t => (φ t).im))) p : ℂ)*Complex.I := by
    funext p
    apply Complex.ext <;> simp [complexFactor]
  rw [he]
  exact (Complex.continuous_ofReal.comp hRc).add
    ((Complex.continuous_ofReal.comp hIc).mul continuous_const)

theorem fullDifference_continuous {φ : ℝ→ℂ} (hφ : Continuous φ) :
    Continuous (fullDifference φ) := by
  unfold fullDifference
  fun_prop

theorem complex_rectangle_factor {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (p : Ambient) :
    fullDifference φ (rectangleMap p)=
      ((-p 1*p 2 : ℝ):ℂ)*complexFactor φ p := by
  have hR : ContDiff ℝ 2 (fun t => (φ t).re) := Complex.reCLM.contDiff.comp hφ
  have hI : ContDiff ℝ 2 (fun t => (φ t).im) := Complex.imCLM.contDiff.comp hφ
  have he : WithLp.toLp 2 ![p 0,p 1,p 2]=p := by ext i; fin_cases i <;> rfl
  have hR' := squareAverage_shared_factor hR (p 0) (p 1) (p 2)
  have hI' := squareAverage_shared_factor hI (p 0) (p 1) (p 2)
  rw [he] at hR' hI'
  have hw : p 0+p 1+(p 0+p 2)-p 0=p 0+p 1+p 2 := by ring
  apply Complex.ext
  · change ((φ (p 0+p 1)+φ (p 0+p 2)-φ (p 0)-
        φ (p 0+p 1+(p 0+p 2)-p 0)).re)=_
    simpa only [hw,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,complexFactor,Collision.rectangleDifference] using hR'
  · change ((φ (p 0+p 1)+φ (p 0+p 2)-φ (p 0)-
        φ (p 0+p 1+(p 0+p 2)-p 0)).im)=_
    simpa only [hw,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,complexFactor,Collision.rectangleDifference] using hI'

theorem fullDifference_lattice {φ : ℝ→ℂ} (hp : Function.Periodic φ period)
    (n : Fin 3→ℤ) (k : Ambient) :
    fullDifference φ (k+latticeShift n)=fullDifference φ k := by
  unfold fullDifference
  rw [periodic_coordinate hp,periodic_coordinate hp,periodic_coordinate hp,periodic_fourth hp]

theorem fullDifference_incoming (φ : ℝ→ℂ) (k : Ambient) :
    fullDifference φ (exchangeIncoming k)=fullDifference φ k := by
  change φ (k 1)+φ (k 0)-φ (k 2)-φ (k 1+k 0-k 2)=_
  simp only [fullDifference,add_comm]

theorem fullDifference_gauge {φ : ℝ→ℂ} (hp : Function.Periodic φ period)
    (swap : Bool) (n m : ℤ) (p : Ambient) :
    fullDifference φ (criticalGauge swap n m p)=fullDifference φ (rectangleMap p) := by
  cases swap <;> simp only [criticalGauge,Bool.false_eq_true,if_false,if_true,
    fullDifference_incoming,fullDifference_lattice hp]

def gaugeZVector (swap : Bool) : Ambient :=
  if swap then exchangeIncoming (rectangleMap (WithLp.toLp 2 ![1,0,0]))
  else rectangleMap (WithLp.toLp 2 ![1,0,0])

theorem criticalGauge_z_hasDerivAt (swap : Bool) (n m : ℤ) (z u v : ℝ) :
    HasDerivAt (fun t : ℝ => criticalGauge swap n m (WithLp.toLp 2 ![t,u,v]))
      (gaugeZVector swap) z := by
  have h := (rectangleMap.hasFDerivAt.comp_hasDerivAt z (parameter_z_hasDerivAt z u v)
    ).add_const (latticeShift ![n,m,0])
  cases swap
  · exact h
  · exact exchangeIncoming.hasFDerivAt.comp_hasDerivAt z h

def factorZDerivative (d : ℝ) : Ambient→ℝ := squareAverage (deriv (deriv (velocity d)))

theorem factorZDerivative_continuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    Continuous (factorZDerivative d) := by
  have h1 : ContDiff ℝ 1 (deriv (velocity d)) :=
    (PinnedClassification.velocity_contDiff hd0 hdU 2).deriv'
  exact squareAverage_continuous (h1.continuous_deriv (by norm_num))

theorem energy_direction_factor {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (swap : Bool) (n m : ℤ) (p : Ambient) :
    (innerSL ℝ (energyGradient d (criticalGauge swap n m p))) (gaugeZVector swap)=
      -p 1*p 2*factorZDerivative d p := by
  have hp : WithLp.toLp 2 ![p 0,p 1,p 2]=p := by ext i; fin_cases i <;> rfl
  have hF := (liftedEnergy_hasFDerivAt hd0 hdU
    (criticalGauge swap n m (WithLp.toLp 2 ![p 0,p 1,p 2]))).comp_hasDerivAt (p 0)
      (criticalGauge_z_hasDerivAt swap n m (p 0) (p 1) (p 2))
  have hG := (sharedFactor_z_hasDerivAt hd0 hdU (p 0) (p 1) (p 2)).const_mul (-p 1*p 2)
  have he : (fun t : ℝ => liftedEnergy d (criticalGauge swap n m
      (WithLp.toLp 2 ![t,p 1,p 2])))=
      (fun t => (-p 1*p 2)*sharedFactor d (WithLp.toLp 2 ![t,p 1,p 2])) := by
    funext t
    rw [criticalGauge_energy,rectangleEnergy_factor hd0 hdU]
    rfl
  dsimp only [Function.comp_def] at hF
  rw [he] at hF
  simpa only [hp] using hF.unique hG

theorem energy_direction_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (swap : Bool) (n m : ℤ) (p : Ambient) :
    |p 1*p 2| * |factorZDerivative d p|≤
      ‖energyGradient d (criticalGauge swap n m p)‖*‖gaugeZVector swap‖ := by
  have h := abs_real_inner_le_norm (energyGradient d (criticalGauge swap n m p))
    (gaugeZVector swap)
  rw [show inner ℝ (energyGradient d (criticalGauge swap n m p)) (gaugeZVector swap)=
    -p 1*p 2*factorZDerivative d p from energy_direction_factor hd0 hdU swap n m p] at h
  simpa only [abs_mul,abs_neg] using h

theorem gauge_difference_local_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hper : Function.Periodic φ period)
    (swap : Bool) (n m : ℤ) (p : Ambient)
    (hgood : sharedFactor d p≠0 ∨ factorZDerivative d p≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 p,
      liftedEnergy d (criticalGauge swap n m q)=0 →
      ‖fullDifference φ (criticalGauge swap n m q)‖≤
        C*‖energyGradient d (criticalGauge swap n m q)‖ := by
  rcases hgood with hG | hJ
  · refine ⟨0,le_rfl,?_⟩
    have hnear := (sharedFactor_contDiff_one hd0 hdU).continuous.continuousAt.eventually_ne hG
    filter_upwards [hnear] with q hqG
    intro hq
    rw [criticalGauge_energy] at hq
    have hzero := (rectangle_zero_set_decomposition hd0 hdU q).mp hq
    rw [fullDifference_gauge hper,complex_rectangle_factor hφ]
    rcases hzero with h0 | h0 | h0
    · simp [h0]
    · simp [h0]
    · exact (hqG h0).elim
  · let a : ℝ := |factorZDerivative d p|/2
    let M : ℝ := ‖complexFactor φ p‖+1
    let L : ℝ := ‖gaugeZVector swap‖
    have ha : 0<a := half_pos (abs_pos.mpr hJ)
    have hM : 0<M := by dsimp [M]; positivity
    have hL : 0≤L := norm_nonneg _
    have hnearA : ∀ᶠ q in 𝓝 p, ‖complexFactor φ q‖<M :=
      (complexFactor_continuous hφ).norm.continuousAt.tendsto.eventually_lt_const
        (by dsimp [M]; linarith)
    have hnearJ : ∀ᶠ q in 𝓝 p, a < |factorZDerivative d q| :=
      (factorZDerivative_continuous hd0 hdU).abs.continuousAt.tendsto.eventually_const_lt
        (half_lt_self (abs_pos.mpr hJ))
    refine ⟨M*L/a,by positivity,?_⟩
    filter_upwards [hnearA,hnearJ] with q hqA hqJ
    intro _
    have hnorm : ‖fullDifference φ (criticalGauge swap n m q)‖=
        |q 1*q 2| * ‖complexFactor φ q‖ := by
      rw [fullDifference_gauge hper,complex_rectangle_factor hφ,norm_mul]
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg]
    have hδ : ‖fullDifference φ (criticalGauge swap n m q)‖≤|q 1*q 2| * M := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hqA.le (abs_nonneg _)
    have hD : a * |q 1*q 2|≤L*‖energyGradient d (criticalGauge swap n m q)‖ := by
      calc
        _ ≤ |q 1*q 2| * |factorZDerivative d q| := by
          nlinarith [abs_nonneg (q 1*q 2)]
        _ ≤ ‖energyGradient d (criticalGauge swap n m q)‖*L :=
          energy_direction_bound hd0 hdU swap n m q
        _ = _ := mul_comm _ _
    have hmul : ‖fullDifference φ (criticalGauge swap n m q)‖*a≤
        M*L*‖energyGradient d (criticalGauge swap n m q)‖ := by
      calc
        _ ≤ (|q 1*q 2| * M)*a := mul_le_mul_of_nonneg_right hδ ha.le
        _ = M*(a * |q 1*q 2|) := by ring
        _ ≤ M*(L*‖energyGradient d (criticalGauge swap n m q)‖) :=
          mul_le_mul_of_nonneg_left hD hM.le
        _ = _ := by ring
    have hC : (M*L/a)*‖energyGradient d (criticalGauge swap n m q)‖=
        (M*L*‖energyGradient d (criticalGauge swap n m q)‖)/a := by ring
    rw [hC]
    exact (le_div_iff₀ ha).mpr hmul

theorem critical_difference_local_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hper : Function.Periodic φ period)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 k, liftedEnergy d q=0 →
      ‖fullDifference φ q‖≤C*‖energyGradient d q‖ := by
  obtain ⟨swap,n,m,z,v,hk,hgood⟩ :=
    every_critical_point_factor_alternative hd0 hdU he hg
  have hgood' : sharedFactor d (WithLp.toLp 2 ![z,0,v])≠0 ∨
      factorZDerivative d (WithLp.toLp 2 ![z,0,v])≠0 := by
    simpa only [(sharedFactor_z_hasDerivAt hd0 hdU z 0 v).deriv] using hgood
  obtain ⟨C,hC,hnear⟩ := gauge_difference_local_gradient_bound hd0 hdU hφ hper
    swap n m (WithLp.toLp 2 ![z,0,v]) hgood'
  have hT : Tendsto (criticalUngauge swap n m) (𝓝 k) (𝓝 (WithLp.toLp 2 ![z,0,v])) := by
    have h := (criticalUngauge_continuous swap n m).continuousAt (x := k) |>.tendsto
    have hi : criticalUngauge swap n m k=WithLp.toLp 2 ![z,0,v] := by
      rw [←hk,criticalUngauge_gauge]
    rwa [hi] at h
  refine ⟨C,hC,?_⟩
  have hq := hT.eventually hnear
  filter_upwards [hq] with q hq
  simpa only [criticalGauge_ungauge] using hq

theorem regular_difference_local_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : Continuous φ) {k : Ambient} (hg : energyGradient d k≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 k,
      ‖fullDifference φ q‖≤C*‖energyGradient d q‖ := by
  let a : ℝ := ‖energyGradient d k‖/2
  let M : ℝ := ‖fullDifference φ k‖+1
  have ha : 0<a := half_pos (norm_pos_iff.mpr hg)
  have hM : 0<M := by dsimp [M]; positivity
  have hδ : ∀ᶠ q in 𝓝 k, ‖fullDifference φ q‖<M :=
    (fullDifference_continuous hφ).norm.continuousAt.tendsto.eventually_lt_const
      (by dsimp [M]; linarith)
  have hG : ∀ᶠ q in 𝓝 k, a<‖energyGradient d q‖ :=
    (energyGradient_continuous hd0 hdU).norm.continuousAt.tendsto.eventually_const_lt
      (half_lt_self (norm_pos_iff.mpr hg))
  refine ⟨M/a,by positivity,?_⟩
  filter_upwards [hδ,hG] with q hqδ hqG
  calc
    _ ≤ M := hqδ.le
    _ = (M/a)*a := by field_simp
    _ ≤ (M/a)*‖energyGradient d q‖ := mul_le_mul_of_nonneg_left hqG.le (by positivity)

/-- A locally bounded complete-difference/gradient quotient on the entire
original energy surface. No individual-leg integrability is used. -/
theorem full_difference_local_gradient_bound {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ) (hper : Function.Periodic φ period) (k : Ambient) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ q in 𝓝 k, liftedEnergy d q=0 →
      ‖fullDifference φ q‖≤C*‖energyGradient d q‖ := by
  by_cases he : liftedEnergy d k=0
  · by_cases hg : energyGradient d k=0
    · exact critical_difference_local_gradient_bound hd0 hdU hφ hper he hg
    · obtain ⟨C,hC,hnear⟩ := regular_difference_local_gradient_bound hd0 hdU hφ.continuous hg
      exact ⟨C,hC,hnear.mono (fun _ h _ => h)⟩
  · refine ⟨0,le_rfl,?_⟩
    have hnear := (liftedEnergy_continuous hd0 hdU).continuousAt.eventually_ne he
    filter_upwards [hnear] with q hq
    exact fun h0 => (hq h0).elim

end
end Resonance.PinnedCriticalCancellation
