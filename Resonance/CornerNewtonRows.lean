import Resonance.CornerNewtonTail

/-! Uniform full-row Newton bounds for the same reference frequency.
The compact core and every input corner layer are included. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.CornerNewtonRows
noncomputable section
open ResonantMeasure CollisionFrequency CornerNewtonEnergy NewtonLayerEnergy NewtonPotentialTails

theorem radius_le_one (n : ℕ) : radius n ≤ 1 := by
  cases n with
  | zero => rfl
  | succ n =>
    apply (CriticalLogShells.shellRadius_le_cutoff n).trans
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)

theorem full_row_bound {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : E,
      (∫⁻ p in cube R, inverseWeight R p * (1+kernelOne (k-p))) ≤ ENNReal.ofReal K := by
  obtain ⟨C,hC,hV⟩ := layer_volume_bounds hR
  obtain ⟨A,hA,hW⟩ := layer_weight_bounds hR
  let B : ℝ := A*(sphereArea+2*C)
  have hB : 0 ≤ B := by
    have := sphereArea_nonnegative
    dsimp [B]
    positivity
  have hn (n : ℕ) (k : E) :
      (∫⁻ p in layer R n, inverseWeight R p*(1+kernelOne (k-p))) ≤
        ENNReal.ofReal (B*coefficient n) := by
    have hr := radius_pos n
    have hbound := one_add_kernelOne_set_bound hr (radius_le_one n) hC
      (layer R n) (layer_measurable R n) (hV n) k
    calc
      _ ≤ ∫⁻ p in layer R n,
          ENNReal.ofReal (A*coefficient n/(radius n)^2)*(1+kernelOne (k-p)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (layer_measurable R n)] with p hp
        exact mul_le_mul_left (hW n p hp) _
      _ = ENNReal.ofReal (A*coefficient n/(radius n)^2)*
          (∫⁻ p in layer R n, 1+kernelOne (k-p)) :=
        lintegral_const_mul _ (show Measurable (fun p : E => 1+kernelOne (k-p)) from
          measurable_const.add (kernelOne_measurable.comp (measurable_const.sub measurable_id)))
      _ ≤ ENNReal.ofReal (A*coefficient n/(radius n)^2)*
          ENNReal.ofReal ((sphereArea+2*C)*(radius n)^2) := mul_le_mul_right hbound _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by have := coefficient_nonnegative n; positivity)]
        congr 1
        dsimp [B]
        field_simp
  refine ⟨B*(∑' n, coefficient n), mul_nonneg hB (tsum_nonneg coefficient_nonnegative), ?_⟩
  intro k
  rw [← layer_union R]
  calc
    _ ≤ ∑' n, ∫⁻ p in layer R n, inverseWeight R p*(1+kernelOne (k-p)) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' n, ENNReal.ofReal (B*coefficient n) := ENNReal.tsum_le_tsum (fun n => hn n k)
    _ = ENNReal.ofReal (B*(∑' n, coefficient n)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hB (coefficient_nonnegative n))
        (coefficient_summable.mul_left B), tsum_mul_left]

theorem reference_newton_row_bound {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : E,
      (∫⁻ p in cube R, ENNReal.ofReal ((referenceFrequency R p)⁻¹) *
        (1+kernelOne (k-p))) ≤ ENNReal.ofReal K := by
  obtain ⟨K,hK,h⟩ := full_row_bound hR
  refine ⟨K,hK,fun k => ?_⟩
  have he : (∫⁻ p in cube R, ENNReal.ofReal ((referenceFrequency R p)⁻¹) *
      (1+kernelOne (k-p))) = ∫⁻ p in cube R, inverseWeight R p*(1+kernelOne (k-p)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet] with p hp
    rw [inverseWeight_on_cube hp]
  rw [he]
  exact h k

end
end Resonance.CornerNewtonRows
