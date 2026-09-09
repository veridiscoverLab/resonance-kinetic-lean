import Resonance.MixedSpatialGN
import Resonance.CubeLinftyCoordinates

/-! Joint spatial/momentum measurability and finite-energy sections of the
same compatible kinetic jet. Zero extension only realizes the existing
cube sections on the ambient actual quartet measure. -/
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.SpatialMomentumSections
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialChainRule SpatialJetSpace SpatialTranslationOrbit
open SpatialIntegrationByParts SpatialThirdGN MixedSpatialGN
set_option maxHeartbeats 1500000

local instance : MeasurableSpace ScalarField:=borel ScalarField
local instance : BorelSpace ScalarField:=⟨rfl⟩

def zeroSection {R : ℝ} (f : C(MomentumDomain R,ScalarField)) : E→ScalarField:=
  Function.extend Subtype.val f (fun _=>0)

theorem zeroSection_on {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    (k : MomentumDomain R) : zeroSection f k=f k :=
  Subtype.val_injective.extend_apply _ _ _

theorem zeroSection_off {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    {k : E} (hk : k∉cube R) : zeroSection f k=0 := by
  apply Function.extend_apply'
  rintro ⟨a,rfl⟩
  exact hk a.property

theorem zeroSection_measurable {R : ℝ} (f : C(MomentumDomain R,ScalarField)) :
    Measurable (zeroSection f) :=
  (MeasurableEmbedding.subtype_coe (FiberContinuity.cube_isClosed R).measurableSet).measurable_extend
    f.continuous.measurable measurable_const

theorem zeroSection_bound {R : ℝ} (f : C(MomentumDomain R,ScalarField)) (k : E) :
    ‖zeroSection f k‖ ≤ ‖f‖ := by
  by_cases hk:k∈cube R
  · rw [show zeroSection f k=f ⟨k,hk⟩ from zeroSection_on f ⟨k,hk⟩]
    exact f.norm_coe_le_norm _
  · rw [zeroSection_off f hk,norm_zero]
    exact norm_nonneg f

def evaluate {R : ℝ} (f : C(MomentumDomain R,ScalarField)) (X : SpatialTorus) (k : E) : ℝ:=
  zeroSection f k X

theorem evaluate_measurable {R : ℝ} (f : C(MomentumDomain R,ScalarField)) :
    Measurable (fun z:SpatialTorus×E=>evaluate f z.1 z.2) := by
  have he : Continuous (fun z:ScalarField×SpatialTorus=>z.1 z.2):=by fun_prop
  exact he.measurable.comp
    (((zeroSection_measurable f).comp measurable_snd).prodMk measurable_fst)

theorem evaluate_bound {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    (X : SpatialTorus) (k : E) : |evaluate f X k| ≤ ‖f‖ :=
  (show |evaluate f X k| ≤ ‖zeroSection f k‖ from (zeroSection f k).norm_coe_le_norm X).trans
    (zeroSection_bound f k)

theorem evaluate_integrable {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable (fun z:SpatialTorus×E=>evaluate f z.1 z.2) (volume.prod μ) := by
  apply Integrable.of_bound (evaluate_measurable f).aestronglyMeasurable ‖f‖
  exact ae_of_all _ (fun z=>evaluate_bound f z.1 z.2)

theorem evaluate_square_integrable {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable (fun z:SpatialTorus×E=>(evaluate f z.1 z.2)^2) (volume.prod μ) := by
  apply Integrable.of_bound ((evaluate_measurable f).pow_const 2).aestronglyMeasurable (‖f‖^2)
  apply ae_of_all
  intro z
  simpa only [Real.norm_eq_abs,abs_pow] using
    pow_le_pow_left₀ (abs_nonneg _) (evaluate_bound f z.1 z.2) 2

theorem evaluate_square_fubini {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    (μ : Measure E) [IsFiniteMeasure μ] :
    (∫z:SpatialTorus×E,(evaluate f z.1 z.2)^2∂volume.prod μ)=
      ∫k,(∫X,(evaluate f X k)^2)∂μ :=
  integral_prod_symm _ (evaluate_square_integrable f μ)

def zeroCubeSection {R : ℝ} (p : JetSpace R) : C(MomentumDomain R,ScalarField):=
  ⟨scalarSection p,by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z:MomentumDomain R×SpatialTorus=>p.val.1 z.2 z.1)
    fun_prop⟩

def firstCubeSection {R : ℝ} (p : JetSpace R) (i : Fin 3) :
    C(MomentumDomain R,ScalarField):=
  ⟨fun k=>direction (scalarFirstField p k) (coordinate i),by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z:MomentumDomain R×SpatialTorus=>p.val.2.1 z.2 (coordinate i) z.1)
    fun_prop⟩

def secondCubeSection {R : ℝ} (p : JetSpace R) (i j : Fin 3) :
    C(MomentumDomain R,ScalarField):=
  ⟨fun k=>secondSection p k (coordinate i) (coordinate j),by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z:MomentumDomain R×SpatialTorus=>
      p.val.2.2.1 z.2 (coordinate i) (coordinate j) z.1)
    fun_prop⟩

def thirdCubeSection {R : ℝ} (p : JetSpace R) (i j l : Fin 3) :
    C(MomentumDomain R,ScalarField):=
  ⟨fun k=>⟨fun X=>p.val.2.2.2 X (coordinate i) (coordinate j) (coordinate l) k,by fun_prop⟩,by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z:MomentumDomain R×SpatialTorus=>
      p.val.2.2.2 z.2 (coordinate i) (coordinate j) (coordinate l) z.1)
    fun_prop⟩

def squareCubeSection {R : ℝ} (p : JetSpace R) : C(MomentumDomain R,ScalarField):=
  ∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,(thirdCubeSection p i j l)^2

theorem squareCubeSection_apply {R : ℝ} (p : JetSpace R) (k : MomentumDomain R)
    (X : SpatialTorus) : squareCubeSection p k X=thirdCoordinateSquare p X k := by
  simp [squareCubeSection,thirdCubeSection,thirdCoordinateSquare]

def massCubeSection {R : ℝ} (p : JetSpace R) : C(MomentumDomain R,ℝ):=
  ⟨fun k=>integralCLM (squareCubeSection p k),integralCLM.continuous.comp (squareCubeSection p).continuous⟩

theorem massCubeSection_apply {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) :
    massCubeSection p k=thirdCoordinateMass p k := by
  apply integral_congr_ae
  exact ae_of_all _ (squareCubeSection_apply p k)

def mass {R : ℝ} (p : JetSpace R) (k : E) : ℝ:=
  integralCLM (zeroSection (squareCubeSection p) k)

theorem mass_measurable {R : ℝ} (p : JetSpace R) : Measurable (mass p) :=
  integralCLM.continuous.measurable.comp (zeroSection_measurable _)

theorem mass_on {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) :
    mass p k=thirdCoordinateMass p k := by
  rw [mass,zeroSection_on]
  exact massCubeSection_apply p k

theorem mass_off {R : ℝ} (p : JetSpace R) {k : E} (hk : k∉cube R) : mass p k=0 := by
  rw [mass,zeroSection_off _ hk,map_zero]

theorem mass_nonnegative {R : ℝ} (p : JetSpace R) (k : E) : 0 ≤ mass p k := by
  by_cases hk:k∈cube R
  · rw [show mass p k=thirdCoordinateMass p ⟨k,hk⟩ from mass_on p ⟨k,hk⟩]
    exact integral_nonneg (fun X=>thirdCoordinateSquare_nonneg p X ⟨k,hk⟩)
  · rw [mass_off p hk]

theorem mass_integrable {R : ℝ} (p : JetSpace R) (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable (mass p) μ := by
  apply Integrable.of_bound (mass_measurable p).aestronglyMeasurable
    (‖integralCLM‖*‖squareCubeSection p‖)
  apply ae_of_all
  intro k
  exact (integralCLM.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (zeroSection_bound _ k) (norm_nonneg integralCLM))

theorem mass_sqrt_memLp {R : ℝ} (p : JetSpace R) (μ : Measure E) [IsFiniteMeasure μ] :
    MemLp (fun k=>Real.sqrt (mass p k)) 2 μ := by
  have hm : AEStronglyMeasurable (fun k=>Real.sqrt (mass p k)) μ:=
    (Real.continuous_sqrt.measurable.comp (mass_measurable p)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  simpa only [Real.sq_sqrt (mass_nonnegative p _)] using mass_integrable p μ

theorem evaluate_on {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    (X : SpatialTorus) (k : MomentumDomain R) : evaluate f X k=f k X := by
  rw [evaluate,zeroSection_on]

theorem evaluate_off {R : ℝ} (f : C(MomentumDomain R,ScalarField))
    (X : SpatialTorus) {k : E} (hk : k∉cube R) : evaluate f X k=0 := by
  rw [evaluate,zeroSection_off f hk]
  rfl

def amplitude {R : ℝ} (p : JetSpace R) (k : E) : ℝ:=‖zeroSection (zeroCubeSection p) k‖

/-- The momentum extension has exactly the same GN estimate everywhere;
off the original cube all sections are zero, not new model states. -/
theorem ambient_coordinate_GN {R : ℝ} (p : JetSpace R) (k : E) (i j : Fin 3) :
    (∫X,(evaluate (firstCubeSection p i) X k)^6) ≤2500*(amplitude p k)^4*mass p k ∧
    (∫X,|evaluate (secondCubeSection p i j) X k|^3) ≤35640*amplitude p k*mass p k := by
  by_cases hk:k∈cube R
  · have he1 : (fun X=>evaluate (firstCubeSection p i) X k)=
        (fun X=>p.val.2.1 X (coordinate i) ⟨k,hk⟩) := by
      funext X
      exact evaluate_on _ X ⟨k,hk⟩
    have he2 : (fun X=>evaluate (secondCubeSection p i j) X k)=
        (fun X=>p.val.2.2.1 X (coordinate i) (coordinate j) ⟨k,hk⟩) := by
      funext X
      exact evaluate_on _ X ⟨k,hk⟩
    have ha : amplitude p k=‖scalarSection p ⟨k,hk⟩‖ := by
      rw [amplitude,show zeroSection (zeroCubeSection p) k=zeroCubeSection p ⟨k,hk⟩ from
        zeroSection_on _ ⟨k,hk⟩]
      rfl
    simp only [congrFun he1,congrFun he2,ha,
      show mass p k=thirdCoordinateMass p ⟨k,hk⟩ from mass_on p ⟨k,hk⟩]
    exact actual_coordinate_GN p ⟨k,hk⟩ i j
  · simp only [evaluate_off _ _ hk,zero_pow (by norm_num : (6:ℕ)≠0),
      abs_zero,zero_pow (by norm_num : (3:ℕ)≠0),integral_zero,mass_off p hk,mul_zero,le_refl,and_self]

theorem square_section_identity {R : ℝ} (p : JetSpace R) (X : SpatialTorus) (k : E) :
    evaluate (squareCubeSection p) X k=
      ∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,(evaluate (thirdCubeSection p i j l) X k)^2 := by
  by_cases hk:k∈cube R
  · simp only [show ∀f:C(MomentumDomain R,ScalarField),evaluate f X k=f ⟨k,hk⟩ X from
      fun f=>evaluate_on f X ⟨k,hk⟩]
    simp [squareCubeSection]
  · simp [evaluate_off _ _ hk]

theorem mass_integral_identity {R : ℝ} (p : JetSpace R) (k : E) :
    mass p k=∫X,∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,(evaluate (thirdCubeSection p i j l) X k)^2 := by
  apply integral_congr_ae
  exact ae_of_all _ (fun X=>square_section_identity p X k)

theorem actual_marginal_finite {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) : IsFiniteMeasure (marginal R θ) := by
  letI:=jointMeasure_finite hR hθ
  unfold marginal
  infer_instance

theorem actual_mass_sqrt_memLp {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) :
    MemLp (fun k=>Real.sqrt (mass p k)) 2 (marginal R θ) := by
  letI:=actual_marginal_finite hR hθ
  exact mass_sqrt_memLp p _

theorem leg_evaluate_measurable {R : ℝ} (f : C(MomentumDomain R,ScalarField)) (i : Fin 4) :
    Measurable (fun z:SpatialTorus×FourMomenta=>evaluate f z.1 (z.2 i)) :=
  (evaluate_measurable f).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem leg_evaluate_square_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f : C(MomentumDomain R,ScalarField)) (i : Fin 4) :
    Integrable (fun z:SpatialTorus×FourMomenta=>(evaluate f z.1 (z.2 i))^2)
      (volume.prod (jointMeasure R θ)) := by
  letI:=jointMeasure_finite hR hθ
  apply Integrable.of_bound ((leg_evaluate_measurable f i).pow_const 2).aestronglyMeasurable (‖f‖^2)
  apply ae_of_all
  intro z
  simpa only [Real.norm_eq_abs,abs_pow] using
    pow_le_pow_left₀ (abs_nonneg _) (evaluate_bound f z.1 (z.2 i)) 2

theorem actual_third_joint_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a : Fin 4) :
    Integrable (fun z:SpatialTorus×FourMomenta=>∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,
      (evaluate (thirdCubeSection p i j l) z.1 (z.2 a))^2) (volume.prod (jointMeasure R θ)) := by
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro l _
  exact leg_evaluate_square_integrable hR hθ _ a

/-- Exact common-history Fubini identity: the same spatial third-order
mass at any actual leg equals its original marginal integral. -/
theorem actual_third_joint_integral {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a : Fin 4) :
    (∫z:SpatialTorus×FourMomenta,∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,
      (evaluate (thirdCubeSection p i j l) z.1 (z.2 a))^2∂volume.prod (jointMeasure R θ))=
      ∫k,mass p k∂marginal R θ := by
  letI:=jointMeasure_finite hR hθ
  letI:=actual_marginal_finite hR hθ
  rw [integral_prod_symm _ (actual_third_joint_integrable hR hθ p a)]
  simp only [←mass_integral_identity]
  exact JointCornerHolder.actual_leg_integral R θ a (mass_integrable p _)

end
end Resonance.SpatialMomentumSections
