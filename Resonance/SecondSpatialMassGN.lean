import Resonance.SpatialMomentumSections

/-! The genuine second-order mass of the same compatible kinetic jet.
This supplies the 1+1 allocation at order two without borrowing third
derivatives or changing the original joint momentum measure. -/
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.SecondSpatialMassGN
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialChainRule SpatialJetSpace SpatialIntegrationByParts SpatialThirdGN
open MixedSpatialGN SpatialMomentumSections
set_option maxHeartbeats 1500000
local instance : MeasurableSpace ScalarField:=borel ScalarField
local instance : BorelSpace ScalarField:=⟨rfl⟩

def square2Section {R : ℝ} (p : JetSpace R) : C(MomentumDomain R,ScalarField):=
  ∑i:Fin 3,∑j:Fin 3,(secondCubeSection p i j)^2

def mass2 {R : ℝ} (p : JetSpace R) (k : E) : ℝ:=
  integralCLM (zeroSection (square2Section p) k)

theorem square2Section_apply {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) (X : SpatialTorus) :
    square2Section p k X=∑i:Fin 3,∑j:Fin 3,(p.val.2.2.1 X (coordinate i) (coordinate j) k)^2 := by
  simp [square2Section,secondCubeSection,secondSection]

theorem mass2_on {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) :
    mass2 p k=∫X,∑i:Fin 3,∑j:Fin 3,(p.val.2.2.1 X (coordinate i) (coordinate j) k)^2 := by
  rw [mass2,zeroSection_on]
  exact integral_congr_ae (ae_of_all _ (square2Section_apply p k))

theorem mass2_off {R : ℝ} (p : JetSpace R) {k : E} (hk : k∉cube R) : mass2 p k=0 := by
  rw [mass2,zeroSection_off _ hk,map_zero]

theorem mass2_nonnegative {R : ℝ} (p : JetSpace R) (k : E) : 0 ≤ mass2 p k := by
  by_cases hk:k∈cube R
  · rw [show mass2 p k=∫X,∑i:Fin 3,∑j:Fin 3,
      (p.val.2.2.1 X (coordinate i) (coordinate j) ⟨k,hk⟩)^2 from mass2_on p ⟨k,hk⟩]
    exact integral_nonneg (fun X=>Finset.sum_nonneg (fun i _=>
      Finset.sum_nonneg (fun j _=>sq_nonneg _)))
  · rw [mass2_off p hk]

theorem mass2_measurable {R : ℝ} (p : JetSpace R) : Measurable (mass2 p) :=
  integralCLM.continuous.measurable.comp (zeroSection_measurable _)

theorem mass2_integrable {R : ℝ} (p : JetSpace R) (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable (mass2 p) μ := by
  apply Integrable.of_bound (mass2_measurable p).aestronglyMeasurable
    (‖integralCLM‖*‖square2Section p‖)
  exact ae_of_all _ (fun k=>(integralCLM.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (zeroSection_bound _ k) (norm_nonneg integralCLM)))

theorem mass2_sqrt_memLp {R : ℝ} (p : JetSpace R) (μ : Measure E) [IsFiniteMeasure μ] :
    MemLp (fun k=>Real.sqrt (mass2 p k)) 2 μ := by
  have hm : AEStronglyMeasurable (fun k=>Real.sqrt (mass2 p k)) μ:=
    (Real.continuous_sqrt.measurable.comp (mass2_measurable p)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  simpa only [Real.sq_sqrt (mass2_nonnegative p _)] using mass2_integrable p μ

theorem actual_mass2_sqrt_memLp {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) :
    MemLp (fun k=>Real.sqrt (mass2 p k)) 2 (marginal R θ) := by
  letI:=actual_marginal_finite hR hθ
  exact mass2_sqrt_memLp p _

theorem second_component_square_le {R : ℝ} (p : JetSpace R)
    (k : MomentumDomain R) (i j : Fin 3) :
    (∫X,(p.val.2.2.1 X (coordinate i) (coordinate j) k)^2) ≤ mass2 p k := by
  rw [mass2_on]
  have hi : Integrable (fun X=>∑a:Fin 3,∑b:Fin 3,
      (p.val.2.2.1 X (coordinate a) (coordinate b) k)^2) :=
    (scalar_integrable (square2Section p k)).congr (ae_of_all _ (square2Section_apply p k))
  have hij : Integrable (fun X:SpatialTorus=>(p.val.2.2.1 X (coordinate i) (coordinate j) k)^2) :=
    (show Continuous (fun X:SpatialTorus=>(p.val.2.2.1 X (coordinate i) (coordinate j) k)^2) by
      fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply integral_mono hij hi
  intro X
  change (p.val.2.2.1 X (coordinate i) (coordinate j) k)^2 ≤
    ∑a:Fin 3,∑b:Fin 3,(p.val.2.2.1 X (coordinate a) (coordinate b) k)^2
  exact (Finset.single_le_sum (fun b _=>sq_nonneg
    (p.val.2.2.1 X (coordinate i) (coordinate b) k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _=>Finset.sum_nonneg (fun b _=>sq_nonneg
        (p.val.2.2.1 X (coordinate a) (coordinate b) k))) (Finset.mem_univ i))

/-- The actual order-two periodic GN estimate, on its own order-two mass. -/
theorem actual_coordinate_second_GN {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) (i : Fin 3) :
    Real.sqrt (∫X,(p.val.2.1 X (coordinate i) k)^4) ≤
      3*‖scalarSection p k‖*Real.sqrt (mass2 p k) := by
  exact (actual_jet_directional_second_GN p k (coordinate i)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (second_component_square_le p k i i)) (by positivity))

theorem ambient_coordinate_second_GN {R : ℝ} (p : JetSpace R) (k : E) (i : Fin 3) :
    Real.sqrt (∫X,(evaluate (firstCubeSection p i) X k)^4) ≤
      3*amplitude p k*Real.sqrt (mass2 p k) := by
  by_cases hk:k∈cube R
  · have he : ∀X,evaluate (firstCubeSection p i) X k=p.val.2.1 X (coordinate i) ⟨k,hk⟩:=
      fun X=>evaluate_on _ X ⟨k,hk⟩
    have ha : amplitude p k=‖scalarSection p ⟨k,hk⟩‖ := by
      rw [amplitude,show zeroSection (zeroCubeSection p) k=zeroCubeSection p ⟨k,hk⟩ from
        zeroSection_on _ ⟨k,hk⟩]
      rfl
    simp only [he,ha]
    exact actual_coordinate_second_GN p ⟨k,hk⟩ i
  · simp only [evaluate_off _ _ hk,zero_pow (by norm_num : (4:ℕ)≠0),integral_zero,
      mass2_off p hk,Real.sqrt_zero,mul_zero,le_refl]

theorem square_product_cauchy (d e : ScalarField) :
    integralCLM ((d*e)^2) ≤ Real.sqrt (integralCLM (d^4))*Real.sqrt (integralCLM (e^4)) := by
  have h:=integral_cauchy (d^2) (e^2)
  have he : d^2*e^2=(d*e)^2:=by ring
  have hd : (d^2)^2=d^4:=by ring
  have hf : (e^2)^2=e^4:=by ring
  rw [he,hd,hf,abs_of_nonneg (square_integral_nonnegative (d*e))] at h
  exact h

theorem actual_two_first_spatial {R : ℝ} (p : JetSpace R) (k l : E)
    (i j : Fin 3) {A B : ℝ} (hk : amplitude p k ≤ A) (hl : amplitude p l ≤ B) :
    (∫X,(evaluate (firstCubeSection p i) X k*evaluate (firstCubeSection p j) X l)^2) ≤
      9*A*B*Real.sqrt (mass2 p k)*Real.sqrt (mass2 p l) := by
  have h:=square_product_cauchy (zeroSection (firstCubeSection p i) k)
    (zeroSection (firstCubeSection p j) l)
  have ha : Real.sqrt (∫X,(evaluate (firstCubeSection p i) X k)^4) ≤
      3*A*Real.sqrt (mass2 p k):=
    (ambient_coordinate_second_GN p k i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk (by norm_num)) (Real.sqrt_nonneg _))
  have hb : Real.sqrt (∫X,(evaluate (firstCubeSection p j) X l)^4) ≤
      3*B*Real.sqrt (mass2 p l):=
    (ambient_coordinate_second_GN p l j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (by norm_num)) (Real.sqrt_nonneg _))
  have hA : 0 ≤ A:=(norm_nonneg _).trans hk
  have hm:=mul_le_mul ha hb (Real.sqrt_nonneg _) (by positivity : 0 ≤ 3*A*Real.sqrt (mass2 p k))
  exact h.trans (hm.trans_eq (by ring))

theorem square2_evaluate_identity {R : ℝ} (p : JetSpace R) (X : SpatialTorus) (k : E) :
    evaluate (square2Section p) X k=
      ∑i:Fin 3,∑j:Fin 3,(evaluate (secondCubeSection p i j) X k)^2 := by
  by_cases hk:k∈cube R
  · simp only [show ∀f:C(MomentumDomain R,ScalarField),evaluate f X k=f ⟨k,hk⟩ X from
      fun f=>evaluate_on f X ⟨k,hk⟩]
    simp [square2Section]
  · simp [evaluate_off _ _ hk]

theorem mass2_integral_identity {R : ℝ} (p : JetSpace R) (k : E) :
    mass2 p k=∫X,∑i:Fin 3,∑j:Fin 3,(evaluate (secondCubeSection p i j) X k)^2 :=
  integral_congr_ae (ae_of_all _ (fun X=>square2_evaluate_identity p X k))

theorem actual_second_joint_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a : Fin 4) :
    Integrable (fun z:SpatialTorus×FourMomenta=>∑i:Fin 3,∑j:Fin 3,
      (evaluate (secondCubeSection p i j) z.1 (z.2 a))^2) (volume.prod (jointMeasure R θ)) := by
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact leg_evaluate_square_integrable hR hθ _ a

/-- Its own original nine-component second mass, not a third-order replacement. -/
theorem actual_second_joint_integral {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a : Fin 4) :
    (∫z:SpatialTorus×FourMomenta,∑i:Fin 3,∑j:Fin 3,
      (evaluate (secondCubeSection p i j) z.1 (z.2 a))^2∂volume.prod (jointMeasure R θ))=
      ∫k,mass2 p k∂marginal R θ := by
  letI:=jointMeasure_finite hR hθ
  letI:=actual_marginal_finite hR hθ
  rw [integral_prod_symm _ (actual_second_joint_integrable hR hθ p a)]
  simp only [←mass2_integral_identity]
  exact JointCornerHolder.actual_leg_integral R θ a (mass2_integrable p _)

end
end Resonance.SecondSpatialMassGN
