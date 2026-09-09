import Resonance.SpatialTranslationOrbit
import Resonance.FixedMultiplier
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Actual directional integration by parts on the original three-dimensional
2π torus. The derivatives are those of its single real lift. This serves the
spatial GN step of the same-quartet H³ energy without differentiating momentum. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.SpatialIntegrationByParts
noncomputable section
open FreeTransport SpatialChainRule SpatialJetSpace SpatialTranslationOrbit
set_option maxHeartbeats 1200000

abbrev ScalarField := C(SpatialTorus,ℝ)
abbrev DerivativeField := C(SpatialTorus,RealPosition→L[ℝ]ℝ)

theorem scalar_integrable (f : ScalarField) : Integrable f (volume:Measure SpatialTorus) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

def integralLinear : ScalarField→ₗ[ℝ]ℝ where
  toFun f:=∫x,f x
  map_add' f g:=integral_add (scalar_integrable f) (scalar_integrable g)
  map_smul' a f:=integral_smul a f

def integralCLM : ScalarField→L[ℝ]ℝ :=
  integralLinear.mkContinuous ((volume:Measure SpatialTorus) univ).toReal (fun f=>by
    change ‖∫x,f x‖≤((volume:Measure SpatialTorus) univ).toReal*‖f‖
    simpa only [Measure.real,mul_comm] using
      norm_integral_le_of_norm_le_const (μ:=(volume:Measure SpatialTorus)) (C:=‖f‖)
        (ae_of_all _ f.norm_coe_le_norm))

theorem integral_translate (f : ScalarField) (x : RealPosition) :
    integralCLM (translateField f x)=integralCLM f :=
  (measurePreserving_add_left (volume:Measure SpatialTorus) (torusQuotient x)).integral_comp
    (Homeomorph.addLeft (torusQuotient x)).toMeasurableEquiv.measurableEmbedding f

def direction (g : DerivativeField) (a : RealPosition) : ScalarField := sectionCLM g a

theorem directional_integral_zero {f : ScalarField} {g : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (a : RealPosition) :
    integralCLM (direction g a)=0 := by
  have h:=integralCLM.hasFDerivAt.comp (0:RealPosition) (translateField_hasFDerivAt hfg 0)
  have he : (integralCLM ∘ translateField f)=(fun _ : RealPosition=>integralCLM f) :=
    funext (integral_translate f)
  rw [he] at h
  have hz:=congrArg (fun A:RealPosition→L[ℝ]ℝ=>A a)
    (h.unique (hasFDerivAt_const (integralCLM f) (0:RealPosition)))
  have hq : torusQuotient (0:RealPosition)=0 := by ext j; rfl
  have ht : translateField g (0:RealPosition)=g := by
    ext X
    simp only [translateField_apply,hq,zero_add]
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,ht,
    sectionOperator,sectionMap,LinearMap.mkContinuous_apply,sectionCLM,direction] using hz

def productDerivative (f h : ScalarField) (g l : DerivativeField) : DerivativeField :=
  ⟨fun X=>f X • l X+h X • g X,by fun_prop⟩

theorem product_graph {f h : ScalarField} {g l : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (hhl : (h,l)∈fieldDerivativeGraph) :
    (f*h,productDerivative f h g l)∈fieldDerivativeGraph := by
  intro x
  exact (hfg x).mul (hhl x)

theorem directional_integration_by_parts {f h : ScalarField} {g l : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (hhl : (h,l)∈fieldDerivativeGraph)
    (a : RealPosition) :
    integralCLM (f*direction l a) = -integralCLM (direction g a*h) := by
  have hz:=directional_integral_zero (product_graph hfg hhl) a
  have he : direction (productDerivative f h g l) a=
      f*direction l a+direction g a*h := by
    ext X
    simp only [direction,sectionCLM_apply,productDerivative,ContinuousMap.coe_mk,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      ContinuousMap.add_apply,ContinuousMap.mul_apply]
    ring
  rw [he,map_add] at hz
  linarith

def powerDerivative (n : ℕ) (f : ScalarField) (g : DerivativeField) : DerivativeField :=
  ⟨fun X=>((n:ℝ)*(f X)^(n-1)) • g X,by fun_prop⟩

theorem power_graph (n : ℕ) {f : ScalarField} {g : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) :
    (f^n,powerDerivative n f g)∈fieldDerivativeGraph := by
  intro x
  change HasFDerivAt (fun y=>f (torusQuotient y)^n)
    (((n:ℝ)*f (torusQuotient x)^(n-1)) • g (torusQuotient x)) x
  simpa only [fieldLift,Function.comp_apply,nsmul_eq_mul] using (hfg x).pow n

/-- The exact periodic identity behind the second-order GN estimate. -/
theorem directional_quartic_identity {f : ScalarField} {g l : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (a : RealPosition)
    (hgl : (direction g a,l)∈fieldDerivativeGraph) :
    integralCLM ((direction g a)^4)=
      -3*integralCLM (f*(direction g a)^2*direction l a) := by
  have hi:=directional_integration_by_parts hfg (power_graph 3 hgl) a
  have he : f*direction (powerDerivative 3 (direction g a) l) a=
      (3:ℝ) • (f*(direction g a)^2*direction l a) := by
    ext X
    simp only [direction,sectionCLM_apply,powerDerivative,ContinuousMap.coe_mk,
      ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousMap.smul_apply,
      ContinuousMap.mul_apply,ContinuousMap.pow_apply]
    norm_num
    ring
  have hr : direction g a*(direction g a)^3=(direction g a)^4 := by ring
  rw [he,hr,map_smul] at hi
  change (3:ℝ)*integralCLM (f*(direction g a)^2*direction l a)=
    -integralCLM ((direction g a)^4) at hi
  linarith

theorem scalar_memLp_two (f : ScalarField) : MemLp f 2 (volume:Measure SpatialTorus) :=
  (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).mpr (scalar_integrable (f^2))

theorem integral_cauchy (f g : ScalarField) :
    |integralCLM (f*g)|≤Real.sqrt (integralCLM (f^2))*Real.sqrt (integralCLM (g^2)) := by
  let hf:=scalar_memLp_two f
  let hg:=scalar_memLp_two g
  have hb:=abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  have he : inner ℝ (hf.toLp f) (hg.toLp g)=integralCLM (f*g) := by
    rw [L2.inner_def]
    change (∫X,_)=(∫X,f X*g X)
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with X hfx hgx
    change (hg.toLp g X)*(hf.toLp f X)=_
    rw [hfx,hgx,mul_comm]
  rw [he] at hb
  have hn (u : ScalarField) (hu : MemLp u 2 (volume:Measure SpatialTorus)) :
      ‖hu.toLp u‖=Real.sqrt (integralCLM (u^2)) := by
    simpa only [Real.norm_eq_abs,sq_abs] using FixedMultiplier.L2_norm_eq_sqrt hu
  rw [hn f hf,hn g hg] at hb
  exact hb

theorem square_integral_nonnegative (f : ScalarField) : 0 ≤ integralCLM (f^2) :=
  integral_nonneg (fun _=>sq_nonneg _)

theorem bounded_multiplier_square (f g : ScalarField) :
    integralCLM ((f*g)^2)≤‖f‖^2*integralCLM (g^2) := by
  have hm : integralCLM ((f*g)^2) ≤ integralCLM ((‖f‖^2) • (g^2)) := by
    apply integral_mono (scalar_integrable _) (scalar_integrable _)
    intro X
    change (f X*g X)^2≤‖f‖^2*(g X)^2
    have hf : (f X)^2≤‖f‖^2 := by
      have hn:=pow_le_pow_left₀ (norm_nonneg (f X)) (f.norm_coe_le_norm X) 2
      simpa only [Real.norm_eq_abs,sq_abs] using hn
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hf (sq_nonneg (g X))
  simpa only [map_smul,smul_eq_mul] using hm

theorem bounded_multiplier_sqrt (f g : ScalarField) :
    Real.sqrt (integralCLM ((f*g)^2))≤‖f‖*Real.sqrt (integralCLM (g^2)) := by
  have hm:=Real.sqrt_le_sqrt (bounded_multiplier_square f g)
  rwa [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)] at hm

theorem weighted_quartic_cauchy (f d e : ScalarField) :
    |integralCLM (f*d^2*e)|≤‖f‖*Real.sqrt (integralCLM (d^4))*
      Real.sqrt (integralCLM (e^2)) := by
  have he : f*d^2*e=d^2*(f*e) := by ring
  rw [he]
  have hb:=integral_cauchy (d^2) (f*e)
  have hp : (d^2)^2=d^4 := by ring
  rw [hp] at hb
  exact hb.trans (by
    calc
      Real.sqrt (integralCLM (d^4))*Real.sqrt (integralCLM ((f*e)^2))
        ≤Real.sqrt (integralCLM (d^4))*(‖f‖*Real.sqrt (integralCLM (e^2))) :=
          mul_le_mul_of_nonneg_left (bounded_multiplier_sqrt f e) (Real.sqrt_nonneg _)
      _ =_ := by ring)

/-- A genuine periodic GN estimate. The supremum is over X for this fixed
momentum reader; the right hand side contains only its second space derivative. -/
theorem directional_second_GN {f : ScalarField} {g l : DerivativeField}
    (hfg : (f,g)∈fieldDerivativeGraph) (a : RealPosition)
    (hgl : (direction g a,l)∈fieldDerivativeGraph) :
    Real.sqrt (integralCLM ((direction g a)^4))≤
      3*‖f‖*Real.sqrt (integralCLM ((direction l a)^2)) := by
  let d:=direction g a
  let e:=direction l a
  have hi:=directional_quartic_identity hfg a hgl
  change integralCLM (d^4)=-3*integralCLM (f*d^2*e) at hi
  have hb:=weighted_quartic_cauchy f d e
  have hn : 0 ≤ integralCLM (d^4) := by
    apply integral_nonneg
    intro X
    change 0≤(d X)^4
    positivity
  by_cases hz : integralCLM (d^4)=0
  · rw [hz,Real.sqrt_zero]
    positivity
  · have hs : 0<Real.sqrt (integralCLM (d^4)) := Real.sqrt_pos.2 (lt_of_le_of_ne hn (Ne.symm hz))
    have hh : (Real.sqrt (integralCLM (d^4)))^2=integralCLM (d^4) := Real.sq_sqrt hn
    have hu:= (abs_le.mp hb).1
    have hm : Real.sqrt (integralCLM (d^4))*Real.sqrt (integralCLM (d^4))≤
        Real.sqrt (integralCLM (d^4))*(3*‖f‖*Real.sqrt (integralCLM (e^2))) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hs).mp (by simpa only [mul_comm] using hm)

def scalarSection {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) : ScalarField :=
  ⟨fun X=>p.val.1 X k,by fun_prop⟩

def scalarFirstField {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) : DerivativeField :=
  ⟨fun X=>(ContinuousMap.evalCLM (R:=ℝ) k).comp (p.val.2.1 X),by fun_prop⟩

def scalarSecondField {R : ℝ} (p : JetSpace R) (k : MomentumDomain R)
    (a : RealPosition) : DerivativeField :=
  ⟨fun X=>(ContinuousMap.evalCLM (R:=ℝ) k).comp
    ((ContinuousLinearMap.apply ℝ (V0 R) a).comp (p.val.2.2.1 X)),by fun_prop⟩

theorem actual_section_graph {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) :
    (scalarSection p k,scalarFirstField p k)∈fieldDerivativeGraph := by
  intro x
  exact (ContinuousMap.evalCLM (R:=ℝ) k).hasFDerivAt.comp x (p.property.1 x)

theorem actual_section_direction_graph {R : ℝ} (p : JetSpace R) (k : MomentumDomain R)
    (a : RealPosition) :
    (direction (scalarFirstField p k) a,scalarSecondField p k a)∈fieldDerivativeGraph := by
  intro x
  exact ((ContinuousMap.evalCLM (R:=ℝ) k).comp
    (ContinuousLinearMap.apply ℝ (V0 R) a)).hasFDerivAt.comp x (p.property.2.1 x)

/-- The GN inequality for the original compatible field at the same k.
The first and second jets are genuine derivatives, not independent fields. -/
theorem actual_jet_directional_second_GN {R : ℝ} (p : JetSpace R)
    (k : MomentumDomain R) (a : RealPosition) :
    Real.sqrt (∫X,(p.val.2.1 X a k)^4)≤
      3*‖scalarSection p k‖*Real.sqrt (∫X,(p.val.2.2.1 X a a k)^2) :=
  directional_second_GN (actual_section_graph p k) a (actual_section_direction_graph p k a)

end
end Resonance.SpatialIntegrationByParts
