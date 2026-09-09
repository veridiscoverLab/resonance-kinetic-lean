import Resonance.NonlinearRegularizedCell

/-! The actual Lambda/c clock of the nonlinear corrector. The original
collision, all five moments, positivity and exact corner values are retained. -/
open Set
namespace Resonance.NonlinearShiftedCorrector
noncomputable section
set_option maxHeartbeats 2200000
open ResonantMeasure Thermodynamics ProfileBanachSmooth RegularizedGraphNorm
open ContinuousSourceCoordinates PhysicalMomentProjection OneWeightedPairReadout

theorem actual_collision_corner_zero {R : ℝ} (hR : 0≤R) (f : X R) (k : cube R)
    (hk : CollisionFrequency.isCubeCorner R k) : FiberContinuity.collisionMap R hR f k=0 := by
  change CollisionFiber.collisionOutput R (FiberContinuity.continuousExtension R f) k=0
  simp only [CollisionFiber.collisionOutput,CollisionFrequency.fiberMeasure_corner_zero hk,
    MeasureTheory.integral_zero_measure]

theorem actual_shifted_corrector_corner {R : ℝ} (hR : 0≤R) (θ : Parameter)
    {Λ c : ℝ} (hΛ : 0<Λ) (q F : X R)
    (he : Λ • q-c • (denominatorMap R θ*FiberContinuity.collisionMap R hR
      (profileMap R θ*(1+q)))=F) (k : cube R)
    (hk : CollisionFrequency.isCubeCorner R k) : q k=F k/Λ := by
  have h := congrArg (fun f : X R=>f k) he
  simp only [ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,
    ContinuousMap.mul_apply,actual_collision_corner_zero hR _ k hk,mul_zero,sub_zero] at h
  exact (eq_div_iff hΛ.ne').mpr (by simpa only [mul_comm] using h)

theorem actual_profile_perturbation_positive {R : ℝ} {θ : Parameter}
    (hθ : θ∈positiveDomain R) (q : X R) (hq : ‖q‖≤(1/2:ℝ)) (k : cube R) :
    0<(profileMap R θ*(1+q)) k := by
  have hb : |q k|≤(1/2:ℝ) := (q.norm_coe_le_norm k).trans hq
  change 0<profileMap R θ k*(1+q k)
  rw [profileMap_apply hθ]
  exact mul_pos (WeightedJointMeasure.profile_pos hθ k.property) (by linarith [(abs_le.mp hb).1])

theorem actual_nonlinear_shifted_corrector {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀θ,(hθ : θ∈K) → ∀Λ c : ℝ,0<Λ → Λ≤c →
      ∀F : X R,‖F‖≤δ*Λ → projection hR (hpos hθ) (sourceMap hR F)=0 →
      ∃q : X R,
        Λ • q-c • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le
          (profileMap R θ*(1+q)))=F ∧
        projection hR (hpos hθ) (sourceMap hR q)=0 ∧
        ‖q‖≤(C/Λ)*‖F‖ ∧ c*‖referenceContinuous hR.le*q‖≤C*‖F‖ ∧
        (∀k : cube R,0<(profileMap R θ*(1+q)) k) ∧
        (∀k : cube R,CollisionFrequency.isCubeCorner R k → q k=F k/Λ) := by
  obtain ⟨δ,C,hδ,hC,hmain⟩ := NonlinearRegularizedCell.actual_nonlinear_regularized_cell hR hK hpos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro θ hθ Λ c hΛ hc F hFn hF
  have hs : 1 ≤ c/Λ := (le_div_iff₀ hΛ).mpr (by simpa using hc)
  have hFn' : ‖Λ⁻¹ • F‖≤δ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le)]
    calc
      _=‖F‖/Λ := by ring
      _≤δ := (div_le_iff₀ hΛ).mpr hFn
  have hF' : projection hR (hpos hθ) (sourceMap hR (Λ⁻¹ • F))=0 := by
    rw [map_smul,map_smul,hF,smul_zero]
  obtain ⟨q,he,hm,hq,hw,hhalf⟩ := hmain θ hθ (c/Λ) hs (Λ⁻¹ • F) hFn' hF'
  have hscale : Λ*(c/Λ)=c := by field_simp
  have hEq : Λ • q-c • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le
      (profileMap R θ*(1+q)))=F := by
    have hh := congrArg (fun f : X R=>Λ • f) he
    simpa only [smul_sub,smul_smul,hscale,mul_inv_cancel₀ hΛ.ne',one_smul] using hh
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le)] at hq hw
  refine ⟨q,hEq,hm,hq.trans_eq (by ring),?_,
    actual_profile_perturbation_positive (hpos hθ) q hhalf,
    actual_shifted_corrector_corner hR.le θ hΛ q F hEq⟩
  have hh := mul_le_mul_of_nonneg_left hw hΛ.le
  convert hh using 1 <;> field_simp

end
end Resonance.NonlinearShiftedCorrector
