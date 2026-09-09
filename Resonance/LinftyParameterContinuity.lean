import Resonance.NormalizedPairParameterBounds

/-! Quantitative parameter continuity of the same original signed
operator on the fixed physical cube L-infinity space.  The input may be
discontinuous; its full output is estimated in C of the closed cube. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.LinftyParameterContinuity
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure Thermodynamics CollisionFrequency ActualPairNormalization
open ActualReferenceRowOperator JointWeightComparison NormalizedPairParameterBounds

def baseRow (R : ℝ) (k p : E) : ℝ :=
  (referenceFrequency R p)⁻¹*baseDensity R k p

theorem baseRow_nonnegative (R : ℝ) (k p : E) : 0≤baseRow R k p :=
  mul_nonneg (CrossRowWeightedBounds.inverseFrequency_nonnegative R p)
    (baseDensity_nonnegative R k p)

theorem baseRow_uniform_bound {R : ℝ} (hR : 0<R) :
    ∃M : ℝ,0≤M ∧ ∀k∈cube R, Integrable (baseRow R k) (cubeVolume R) ∧
      (∫p,baseRow R k p∂cubeVolume R)≤M := by
  have hu := unitParameter_positive R
  obtain ⟨M1,hM1,h1⟩ := ContinuousRowOperator.rowNorm_uniform_bound
    (incomingRow R unitParameter) (incomingRow_integrable hR hu) (incomingRow_L1_continuous hR hu)
  obtain ⟨M2,hM2,h2⟩ := ContinuousRowOperator.rowNorm_uniform_bound
    (crossRow R unitParameter) (crossRow_integrable hR hu) (crossRow_L1_continuous hR hu)
  refine ⟨M1+2*M2,by positivity,?_⟩
  intro k hk
  let ks : cube R := ⟨k,hk⟩
  have he (p : cube R) : baseRow R k p=incomingRow R unitParameter ks p+
      2*crossRow R unitParameter ks p := by
    unfold baseRow baseDensity incomingRow crossRow
    ring
  have hi : Integrable (fun p : cube R => baseRow R k p) (cubeMeasure R) := by
    simp_rw [he]
    exact (incomingRow_integrable hR hu ks).add ((crossRow_integrable hR hu ks).const_mul 2)
  refine ⟨(integrableOn_iff_comap_subtypeVal
    (FiberContinuity.cube_isClosed R).measurableSet).mpr hi,?_⟩
  change (∫p in cube R,baseRow R k p)≤_
  rw [←integral_subtype_comap (FiberContinuity.cube_isClosed R).measurableSet (baseRow R k)]
  change (∫p,baseRow R k p∂cubeMeasure R)≤_
  simp_rw [he]
  rw [integral_add (incomingRow_integrable hR hu ks)
    ((crossRow_integrable hR hu ks).const_mul 2),integral_const_mul]
  have hi1 (p : cube R) : ‖incomingRow R unitParameter ks p‖=incomingRow R unitParameter ks p :=
    Real.norm_of_nonneg (mul_nonneg (CrossRowWeightedBounds.inverseFrequency_nonnegative R p)
      ENNReal.toReal_nonneg)
  have hi2 (p : cube R) : ‖crossRow R unitParameter ks p‖=crossRow R unitParameter ks p :=
    Real.norm_of_nonneg (mul_nonneg (CrossRowWeightedBounds.inverseFrequency_nonnegative R p)
      ENNReal.toReal_nonneg)
  have hb1 := h1 ks
  have hb2 := h2 ks
  simp_rw [hi1] at hb1
  simp_rw [hi2] at hb2
  linarith

theorem geometricFrequency_positive_ae {R : ℝ} (hR : 0<R) :
    ∀ᵐ p∂cubeVolume R,0<geometricFrequency R p := by
  filter_upwards [FiveInvariantFinal.cube_ae_openCube R] with p hp
  exact CollisionFrequencyPositive.geometricFrequency_noncorner_positive hR
    (fun i=>(hp i).le) (fun hc=>(ne_of_lt (hp 0)) (hc 0))

theorem compact_continuousOutput_difference_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀(θ : Parameter)(hθ : θ∈K)(β : Parameter)(hβ : β∈K),
      ‖AmbientLinftyCompact.continuousOutput hR (hpos hθ)-
        AmbientLinftyCompact.continuousOutput hR (hpos hβ)‖≤C*‖θ-β‖ := by
  obtain ⟨C,hC,hb⟩ := compact_kernel_reference_bound hR.le hK hpos
  obtain ⟨M,hM,hrow⟩ := baseRow_uniform_bound hR
  refine ⟨C*M,mul_nonneg hC hM,?_⟩
  intro θ hθ β hβ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro k
  change ‖AmbientLinftyCompact.continuousOutput hR (hpos hθ) f k-
    AmbientLinftyCompact.continuousOutput hR (hpos hβ) f k‖≤_
  obtain ⟨hiθ,heθ⟩ := AmbientLinftyCompact.continuousOutput_integrable_apply hR (hpos hθ) f k
  obtain ⟨hiβ,heβ⟩ := AmbientLinftyCompact.continuousOutput_integrable_apply hR (hpos hβ) f k
  rw [heθ,heβ,←integral_sub hiθ hiβ]
  have hd : ‖∫p,AmbientLinftyCompact.kernel R θ k p*f p-
      AmbientLinftyCompact.kernel R β k p*f p∂cubeVolume R‖≤
      ∫p,(C*‖θ-β‖*‖f‖)*baseRow R k p∂cubeVolume R := by
    apply norm_integral_le_of_norm_le ((hrow k k.property).1.const_mul _)
    filter_upwards [ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet,
      geometricFrequency_positive_ae hR,LinftyRowOperator.ae_norm_bound f] with p hp hg hf
    rw [←sub_mul,norm_mul,Real.norm_eq_abs]
    calc
      _ ≤ (C*‖θ-β‖*baseRow R k p)*‖f‖ :=
        mul_le_mul (hb θ hθ β hβ k k.property p hp hg) hf (norm_nonneg _) (by
          exact mul_nonneg (mul_nonneg hC (norm_nonneg _)) (baseRow_nonnegative R k p))
      _ = _ := by ring
  apply hd.trans
  rw [integral_const_mul]
  calc
    _ ≤ (C*‖θ-β‖*‖f‖)*M := mul_le_mul_of_nonneg_left (hrow k k.property).2 (by positivity)
    _ = _ := by ring

theorem compact_operator_difference_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀(θ : Parameter)(hθ : θ∈K)(β : Parameter)(hβ : β∈K),
      ‖AmbientLinftyCompact.operator hR (hpos hθ)-
        AmbientLinftyCompact.operator hR (hpos hβ)‖≤C*‖θ-β‖ := by
  obtain ⟨C,hC,hb⟩ := compact_continuousOutput_difference_bound hR hK hpos
  refine ⟨C,hC,?_⟩
  intro θ hθ β hβ
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro f
  change ‖CubeLinftyCoordinates.embed R (AmbientLinftyCompact.continuousOutput hR (hpos hθ) f)-
    CubeLinftyCoordinates.embed R (AmbientLinftyCompact.continuousOutput hR (hpos hβ) f)‖≤_
  rw [←map_sub]
  exact (CubeLinftyCoordinates.extendVector_bound R _).trans
    (((AmbientLinftyCompact.continuousOutput hR (hpos hθ)-
      AmbientLinftyCompact.continuousOutput hR (hpos hβ)).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (hb θ hθ β hβ) (norm_nonneg f)))

end
end Resonance.LinftyParameterContinuity
