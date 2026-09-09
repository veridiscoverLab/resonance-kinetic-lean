import Resonance.OneWeightedPairReadout
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual full support of closed-cube Lebesgue measure for continuous
readouts. The ambient L∞ embedding is isometric for R>0, including the
boundary and all corners; this is proved, not inferred from its upper bound. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CubeContinuousEssentialNorm
noncomputable section
set_option maxHeartbeats 1400000
open ResonantMeasure FiberContinuity ActualPairNormalization CubeLinftyCoordinates

theorem cube_convex (R : ℝ) : Convex ℝ (cube R) := by
  intro x hx y hy a b ha hb hab i
  change |a*x i+b*y i|≤R
  calc
    _ ≤ |a*x i|+|b*y i| := abs_add_le _ _
    _ = a*|x i|+b*|y i| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = R := by rw [←add_mul,hab,one_mul]

theorem cube_interior_nonempty {R : ℝ} (hR : 0<R) : (interior (cube R)).Nonempty := by
  have hb : Metric.ball (0:E) R⊆cube R := by
    intro k hk i
    have hn : ‖k‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hk
    exact ((by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le k i) : |k i|≤‖k‖).trans hn.le
  exact ⟨0,(interior_maximal hb Metric.isOpen_ball) (Metric.mem_ball_self hR)⟩

theorem cube_subset_closure_interior {R : ℝ} (hR : 0<R) : cube R⊆closure (interior (cube R)) := by
  rw [(cube_convex R).closure_interior_eq_closure_of_nonempty_interior (cube_interior_nonempty hR)]
  exact subset_closure

theorem continuous_ae_bound {R : ℝ} (hR : 0<R) (u : C(cube R,ℝ)) {B : ℝ}
    (hb : ∀ᵐk∂cubeVolume R,‖zeroExtension R u k‖≤B) : ∀k : cube R,‖u k‖≤B := by
  let f : E→ℝ := fun k=>‖continuousExtension R u k‖
  have he : f=ᵐ[cubeVolume R] fun k=>min (f k) B := by
    filter_upwards [hb,ae_restrict_mem (measurable_cube R)] with k hb hk
    have hfk : f k=‖zeroExtension R u k‖ := by
      rw [zeroExtension_apply R u ⟨k,hk⟩]
      exact congrArg norm (continuousExtension_eq R u ⟨k,hk⟩)
    exact (min_eq_left (hfk.trans_le hb)).symm
  have hf : Continuous f := (continuousExtension R u).continuous.norm
  have hp := MeasureTheory.Measure.eqOn_of_ae_eq (μ:=(volume : Measure E)) he hf.continuousOn
    (hf.min continuous_const).continuousOn (cube_subset_closure_interior hR)
  intro k
  have hh : f k≤B := (hp k.property).trans_le (min_le_right _ _)
  simpa only [f,continuousExtension_eq R u k] using hh

theorem embed_norm_eq {R : ℝ} (hR : 0<R) (u : C(cube R,ℝ)) : ‖embed R u‖=‖u‖ := by
  apply le_antisymm (extendVector_bound R u)
  apply (ContinuousMap.norm_le _ (norm_nonneg (embed R u))).mpr
  apply continuous_ae_bound hR u
  filter_upwards [LinftyRowOperator.ae_norm_bound (embed R u),embed_ae R u] with k hn he
  rwa [he] at hn

theorem continuous_ae_eq {R : ℝ} (hR : 0<R) (u v : C(cube R,ℝ))
    (he : zeroExtension R u=ᵐ[cubeVolume R] zeroExtension R v) : u=v := by
  have h : embed R u=embed R v := by
    apply MeasureTheory.Lp.ext
    exact (embed_ae R u).trans (he.trans (embed_ae R v).symm)
  have hn : ‖u-v‖=0 := by rw [←embed_norm_eq hR,map_sub,h,sub_self,norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

def embedIsometry {R : ℝ} (hR : 0<R) : C(cube R,ℝ)→ₗᵢ[ℝ]LinftyMultiplication.X R :=
  ⟨(embed R).toLinearMap,embed_norm_eq hR⟩

end
end Resonance.CubeContinuousEssentialNorm
