import Resonance.SpatialIntegrationByParts
import Resonance.JointCornerHolder
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Third-order periodic directional GN estimates, keeping the true real
lift and handling the zero set of the second derivative explicitly. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.SpatialThirdGN
noncomputable section
open FreeTransport SpatialChainRule SpatialJetSpace SpatialTranslationOrbit
open SpatialIntegrationByParts
set_option maxHeartbeats 1500000

def signedSquare (x : ℝ) : ℝ:=x*|x|

theorem signedSquare_hasDerivAt (x : ℝ) : HasDerivAt signedSquare (2*|x|) x := by
  rcases lt_trichotomy x 0 with hx|rfl|hx
  · have h:=(hasDerivAt_id x).mul (hasDerivAt_abs_neg hx)
    have he : 2*|x|=1*|x|+x*(-1) := by rw [abs_of_neg hx]; ring
    rw [he]
    exact h
  · rw [show 2*|(0:ℝ)|=0 by norm_num,hasDerivAt_iff_tendsto_slope]
    have he : slope signedSquare 0=fun y:ℝ=>|y| := by
      funext y
      by_cases hy:y=0
      · simp [hy,slope,signedSquare]
      · simp [slope,signedSquare,hy,smul_eq_mul]
    rw [he]
    simpa only [abs_zero] using (continuous_abs.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  · have h:=(hasDerivAt_id x).mul (hasDerivAt_abs_pos hx)
    have he : 2*|x|=1*|x|+x*1 := by rw [abs_of_pos hx]; ring
    rw [he]
    exact h

def signedSquareField (f : ScalarField) : ScalarField :=
  ⟨fun X=>signedSquare (f X),f.continuous.mul f.continuous.abs⟩

def signedSquareDerivative (f : ScalarField) (g : DerivativeField) : DerivativeField :=
  ⟨fun X=>(2*|f X|) • g X,by fun_prop⟩

theorem signedSquare_graph {f : ScalarField} {g : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) :
    (signedSquareField f,signedSquareDerivative f g)∈fieldDerivativeGraph := by
  intro x
  exact (signedSquare_hasDerivAt (f (torusQuotient x))).comp_hasFDerivAt x (hfg x)

/-- The complete sixth-power identity on the actual periodic domain. -/
theorem directional_sixth_identity {f : ScalarField} {g l : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (a : RealPosition)
    (hgl : (direction g a,l)∈fieldDerivativeGraph) :
    integralCLM ((direction g a)^6)=
      -5*integralCLM (f*(direction g a)^4*direction l a) := by
  have hi:=directional_integration_by_parts hfg (power_graph 5 hgl) a
  have he : f*direction (powerDerivative 5 (direction g a) l) a=
      (5:ℝ) • (f*(direction g a)^4*direction l a) := by
    ext X
    simp only [direction,sectionCLM_apply,powerDerivative,ContinuousMap.coe_mk,
      ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousMap.smul_apply,
      ContinuousMap.mul_apply,ContinuousMap.pow_apply]
    norm_num
    ring
  have hr : direction g a*(direction g a)^5=(direction g a)^6 := by ring
  rw [he,hr,map_smul] at hi
  change (5:ℝ)*integralCLM (f*(direction g a)^4*direction l a)=
    -integralCLM ((direction g a)^6) at hi
  linarith

def absField (f : ScalarField) : ScalarField:=⟨fun X=>|f X|,f.continuous.abs⟩

/-- The |second derivative|³ identity is valid also at its zeros: the
signed square above has an actual derivative there, with no division by it. -/
theorem directional_second_cubic_identity {d : ScalarField} {g l : DerivativeField}
    (hdg : (d,g)∈fieldDerivativeGraph) (a : RealPosition)
    (hgl : (direction g a,l)∈fieldDerivativeGraph) :
    integralCLM ((absField (direction g a))^3)=
      -2*integralCLM (d*absField (direction g a)*direction l a) := by
  have hi:=directional_integration_by_parts hdg (signedSquare_graph hgl) a
  have he : d*direction (signedSquareDerivative (direction g a) l) a=
      (2:ℝ) • (d*absField (direction g a)*direction l a) := by
    ext X
    simp only [direction,sectionCLM_apply,signedSquareDerivative,ContinuousMap.coe_mk,
      ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousMap.smul_apply,
      ContinuousMap.mul_apply,absField]
    ring
  have hr : direction g a*signedSquareField (direction g a)=(absField (direction g a))^3 := by
    ext X
    change (direction g a X)*(direction g a X*|direction g a X|)=|direction g a X|^3
    calc
      (direction g a X)*(direction g a X*|direction g a X|)
        =(direction g a X)^2*|direction g a X| := by ring
      _ =|direction g a X|^2*|direction g a X| := by rw [sq_abs]
      _ =_ := by ring
  rw [he,hr,map_smul] at hi
  change (2:ℝ)*integralCLM (d*absField (direction g a)*direction l a)=
    -integralCLM ((absField (direction g a))^3) at hi
  linarith

theorem abs_integral_le (f : ScalarField) : |integralCLM f| ≤ integralCLM (absField f) := by
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (μ:=(volume:Measure SpatialTorus)) f)

theorem abs_integral_mul_le (f h : ScalarField) :
    |integralCLM (f*h)|≤‖f‖*integralCLM (absField h) := by
  apply (abs_integral_le (f*h)).trans
  have hm : integralCLM (absField (f*h)) ≤ integralCLM (‖f‖ • absField h) := by
    apply integral_mono (scalar_integrable _) (scalar_integrable _)
    intro X
    change |f X*h X|≤‖f‖*|h X|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm X)
      (abs_nonneg _)
  simpa only [map_smul,smul_eq_mul] using hm

theorem abs_even_sixth (d : ScalarField) : (absField d)^6=d^6 := by
  ext X
  change |d X|^6=(d X)^6
  rw [show (6:ℕ)=2*3 by norm_num,pow_mul,pow_mul,sq_abs]

theorem mixed_four_one_holder (d e : ScalarField) :
    integralCLM (absField (d^4*e))≤
      (integralCLM (d^6))^((2:ℝ)/3)*(integralCLM ((absField e)^3))^((1:ℝ)/3) := by
  have hb:=JointCornerHolder.holder_two_one (scalar_integrable ((absField d)^6))
    (scalar_integrable ((absField e)^3))
    (fun X=>pow_nonneg (abs_nonneg (d X)) 6)
    (fun X=>pow_nonneg (abs_nonneg (e X)) 3)
  have he : (fun X:SpatialTorus=>(|d X|^6)^((2:ℝ)/3)*(|e X|^3)^((1:ℝ)/3))=
      (fun X=>|(d X)^4*e X|) := by
    funext X
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _),
      ←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    norm_num
  change (∫X,(|d X|^6)^((2:ℝ)/3)*(|e X|^3)^((1:ℝ)/3))≤_ at hb
  rw [he] at hb
  change integralCLM (absField (d^4*e))≤
    (integralCLM ((absField d)^6))^((2:ℝ)/3)*(integralCLM ((absField e)^3))^((1:ℝ)/3) at hb
  rw [abs_even_sixth] at hb
  exact hb

theorem mixed_two_two_holder (d e : ScalarField) :
    integralCLM ((d*absField e)^2)≤
      (integralCLM ((absField e)^3))^((2:ℝ)/3)*(integralCLM (d^6))^((1:ℝ)/3) := by
  have hb:=JointCornerHolder.holder_two_one (scalar_integrable ((absField e)^3))
    (scalar_integrable ((absField d)^6))
    (fun X=>pow_nonneg (abs_nonneg (e X)) 3)
    (fun X=>pow_nonneg (abs_nonneg (d X)) 6)
  have he : (fun X:SpatialTorus=>(|e X|^3)^((2:ℝ)/3)*(|d X|^6)^((1:ℝ)/3))=
      (fun X=>(d X*|e X|)^2) := by
    funext X
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _),
      ←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    norm_num
    simp only [sq_abs,mul_pow]
    ring
  change (∫X,(|e X|^3)^((2:ℝ)/3)*(|d X|^6)^((1:ℝ)/3))≤_ at hb
  rw [he] at hb
  change integralCLM ((d*absField e)^2)≤
    (integralCLM ((absField e)^3))^((2:ℝ)/3)*(integralCLM ((absField d)^6))^((1:ℝ)/3) at hb
  rw [abs_even_sixth] at hb
  exact hb

theorem sqrt_fractional_product {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    Real.sqrt (x^((2:ℝ)/3)*y^((1:ℝ)/3))=x^((1:ℝ)/3)*y^((1:ℝ)/6) := by
  rw [Real.sqrt_mul (Real.rpow_nonneg hx _),Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul hx,←Real.rpow_mul hy]
  norm_num

theorem directional_sixth_coupled {f : ScalarField} {g l : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (a : RealPosition)
    (hgl : (direction g a,l)∈fieldDerivativeGraph) :
    integralCLM ((direction g a)^6)≤5*‖f‖*
      (integralCLM ((direction g a)^6))^((2:ℝ)/3)*
      (integralCLM ((absField (direction l a))^3))^((1:ℝ)/3) := by
  let d:=direction g a
  let e:=direction l a
  have hi:=directional_sixth_identity hfg a hgl
  change integralCLM (d^6)=-5*integralCLM (f*d^4*e) at hi
  have hb:=abs_integral_mul_le f (d^4*e)
  have he : f*(d^4*e)=f*d^4*e := by ring
  rw [he] at hb
  have hbound:=mul_le_mul_of_nonneg_left (mixed_four_one_holder d e) (norm_nonneg f)
  have hfinal:=hb.trans hbound
  have hlo : -((‖f‖)*(integralCLM (d^6))^((2:ℝ)/3)*
      (integralCLM ((absField e)^3))^((1:ℝ)/3)) ≤ integralCLM (f*d^4*e) := by
    simpa only [mul_assoc] using (abs_le.mp hfinal).1
  nlinarith

theorem directional_second_cubic_coupled {d : ScalarField} {g l : DerivativeField}
    (hdg : (d,g)∈fieldDerivativeGraph) (a : RealPosition)
    (hgl : (direction g a,l)∈fieldDerivativeGraph) :
    integralCLM ((absField (direction g a))^3)≤
      2*(integralCLM ((absField (direction g a))^3))^((1:ℝ)/3)*
        (integralCLM (d^6))^((1:ℝ)/6)*Real.sqrt (integralCLM ((direction l a)^2)) := by
  let e:=direction g a
  let h:=direction l a
  have hi:=directional_second_cubic_identity hdg a hgl
  change integralCLM ((absField e)^3)=-2*integralCLM (d*absField e*h) at hi
  have hb:=integral_cauchy (d*absField e) h
  have hE : 0 ≤ integralCLM ((absField e)^3) :=
    integral_nonneg (fun X=>pow_nonneg (abs_nonneg (e X)) 3)
  have hD : 0 ≤ integralCLM (d^6) := by
    apply integral_nonneg
    intro X
    change 0≤(d X)^6
    positivity
  have hs:=Real.sqrt_le_sqrt (mixed_two_two_holder d e)
  rw [sqrt_fractional_product hE hD] at hs
  have hfinal:=hb.trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))
  have hlo:=(abs_le.mp hfinal).1
  nlinarith

theorem coupled_scalar_powers {A B C M : ℝ} (hB : 0≤B)
    (hM : 0≤M) (h1 : A^2≤5*M*B) (h2 : B^2≤2*A*C) :
    A^6≤2500*M^4*C^2 ∧ B^3≤20*M*C^2 := by
  have hB3 : B^3≤20*M*C^2 := by
    by_cases hz:B=0
    · rw [hz,zero_pow (by norm_num : (3:ℕ)≠0)]
      positivity
    · have hp : 0<B:=lt_of_le_of_ne hB (Ne.symm hz)
      have hb4:=pow_le_pow_left₀ (sq_nonneg B) h2 2
      have ha4:=mul_le_mul_of_nonneg_right h1 (by positivity:0≤4*C^2)
      apply (mul_le_mul_iff_left₀ hp).mp
      calc
        B^3*B=(B^2)^2 := by ring
        _ ≤(2*A*C)^2 := hb4
        _ =A^2*(4*C^2) := by ring
        _ ≤(5*M*B)*(4*C^2) := ha4
        _ =(20*M*C^2)*B := by ring
  refine ⟨?_,hB3⟩
  calc
    A^6=(A^2)^3 := by ring
    _ ≤(5*M*B)^3 := pow_le_pow_left₀ (sq_nonneg A) h1 3
    _ =125*M^3*B^3 := by ring
    _ ≤125*M^3*(20*M*C^2) := mul_le_mul_of_nonneg_left hB3 (by positivity)
    _ =2500*M^4*C^2 := by ring

theorem coupled_integral_powers {S T U M : ℝ} (hS : 0≤S) (hT : 0≤T)
    (hU : 0≤U) (hM : 0≤M)
    (h1 : S≤5*M*S^((2:ℝ)/3)*T^((1:ℝ)/3))
    (h2 : T≤2*T^((1:ℝ)/3)*S^((1:ℝ)/6)*Real.sqrt U) :
    S≤2500*M^4*U ∧ T≤20*M*U := by
  let A:=S^((1:ℝ)/6)
  let B:=T^((1:ℝ)/3)
  let C:=Real.sqrt U
  have hA : 0≤A:=Real.rpow_nonneg hS _
  have hB : 0≤B:=Real.rpow_nonneg hT _
  have hC : 0≤C:=Real.sqrt_nonneg _
  have hA6 : A^6=S := by
    dsimp only [A]
    rw [←Real.rpow_natCast,←Real.rpow_mul hS]
    norm_num
  have hA4 : A^4=S^((2:ℝ)/3) := by
    dsimp only [A]
    rw [←Real.rpow_natCast,←Real.rpow_mul hS]
    norm_num
  have hB3 : B^3=T := by
    dsimp only [B]
    rw [←Real.rpow_natCast,←Real.rpow_mul hT]
    norm_num
  have hC2 : C^2=U:=Real.sq_sqrt hU
  have hc1 : A^2≤5*M*B := by
    by_cases hz:A=0
    · rw [hz,zero_pow (by norm_num : (2:ℕ)≠0)]
      positivity
    · have hp : 0<A:=lt_of_le_of_ne hA (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ (pow_pos hp 4)).mp
      have hh : A^6≤5*M*A^4*B := by rw [hA6,hA4]; exact h1
      nlinarith
  have hc2 : B^2≤2*A*C := by
    by_cases hz:B=0
    · rw [hz,zero_pow (by norm_num : (2:ℕ)≠0)]
      positivity
    · have hp : 0<B:=lt_of_le_of_ne hB (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hp).mp
      have hh : B^3≤2*B*A*C := by rw [hB3]; exact h2
      nlinarith
  have hb:=coupled_scalar_powers hB hM hc1 hc2
  simpa only [hA6,hB3,hC2] using hb

/-- Both actual third-order GN estimates, with explicit constants and all
zero cases included. The graph hypotheses are genuine derivatives on T³. -/
theorem directional_third_GN {f : ScalarField} {g l m : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (a : RealPosition)
    (hgl : (direction g a,l)∈fieldDerivativeGraph)
    (hlm : (direction l a,m)∈fieldDerivativeGraph) :
    integralCLM ((direction g a)^6)≤2500*‖f‖^4*integralCLM ((direction m a)^2) ∧
    integralCLM ((absField (direction l a))^3)≤20*‖f‖*integralCLM ((direction m a)^2) := by
  have hS : 0 ≤ integralCLM ((direction g a)^6) := by
    apply integral_nonneg
    intro X
    change 0≤(direction g a X)^6
    positivity
  have hT : 0 ≤ integralCLM ((absField (direction l a))^3) :=
    integral_nonneg (fun X=>pow_nonneg (abs_nonneg (direction l a X)) 3)
  exact coupled_integral_powers hS hT (square_integral_nonnegative (direction m a))
    (norm_nonneg f) (directional_sixth_coupled hfg a hgl)
      (directional_second_cubic_coupled hgl a hlm)

def scalarThirdField {R : ℝ} (p : JetSpace R) (k : MomentumDomain R)
    (a : RealPosition) : DerivativeField :=
  ⟨fun X=>(ContinuousMap.evalCLM (R:=ℝ) k).comp
    (((ContinuousLinearMap.apply ℝ (V0 R) a).comp (ContinuousLinearMap.apply ℝ (V1 R) a)).comp
      (p.val.2.2.2 X)),by fun_prop⟩

theorem actual_section_second_direction_graph {R : ℝ} (p : JetSpace R)
    (k : MomentumDomain R) (a : RealPosition) :
    (direction (scalarSecondField p k a) a,scalarThirdField p k a)∈fieldDerivativeGraph := by
  intro x
  exact ((ContinuousMap.evalCLM (R:=ℝ) k).comp
    ((ContinuousLinearMap.apply ℝ (V0 R) a).comp
      (ContinuousLinearMap.apply ℝ (V1 R) a))).hasFDerivAt.comp x (p.property.2.2 x)

/-- Instantiation on the same actual compatible kinetic field at each
original momentum. Only its existing 0–3 spatial jets are used. -/
theorem actual_jet_directional_third_GN {R : ℝ} (p : JetSpace R)
    (k : MomentumDomain R) (a : RealPosition) :
    (∫X,(p.val.2.1 X a k)^6)≤2500*‖scalarSection p k‖^4*
      (∫X,(p.val.2.2.2 X a a a k)^2) ∧
    (∫X,|p.val.2.2.1 X a a k|^3)≤20*‖scalarSection p k‖*
      (∫X,(p.val.2.2.2 X a a a k)^2) :=
  directional_third_GN (actual_section_graph p k) a (actual_section_direction_graph p k a)
    (actual_section_second_direction_graph p k a)

end
end Resonance.SpatialThirdGN
