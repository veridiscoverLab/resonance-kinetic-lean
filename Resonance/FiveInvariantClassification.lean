import Resonance.CollisionLocalization
import Resonance.CollisionCoefficientUniqueness

/-! One global coefficient vector for the original measurable collision
invariant. A countable exhaustion preserves every interior momentum point;
overlap uniqueness prevents independent local polynomial choices. -/
open Set MeasureTheory Filter
open scoped Topology

namespace Resonance.FiveInvariantClassification
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants QuadraticPointwiseClosure
open CollisionLocalization CollisionCoefficientUniqueness

def innerRadius (R : ℝ) (n : ℕ) : ℝ := R-(R/2)/((n:ℝ)+1)

theorem innerRadius_bounds {R : ℝ} (hR : 0<R) (n : ℕ) :
    R/2 ≤ innerRadius R n ∧ innerRadius R n < R := by
  have hp : 0<(R/2)/((n:ℝ)+1) := by positivity
  have hb : (R/2)/((n:ℝ)+1) ≤ R/2 := by
    apply (div_le_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  dsimp [innerRadius]
  constructor <;> linarith

theorem innerRadius_tendsto (R : ℝ) : Tendsto (innerRadius R) atTop (𝓝 R) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (R/2)
  simpa only [innerRadius,mul_one_div,mul_zero,sub_zero] using tendsto_const_nhds.sub h

theorem inner_cubes_exhaust {R : ℝ} (hR : 0<R) : openCube R = ⋃n,openCube (innerRadius R n) := by
  ext x
  constructor
  · intro hx
    have hj (j : Fin 3) : ∀ᶠ n in atTop, |x j| < innerRadius R n :=
      (tendsto_order.mp (innerRadius_tendsto R)).1 _ (hx j)
    obtain ⟨n,hn⟩ := (eventually_all.mpr hj).exists
    exact mem_iUnion.mpr ⟨n,hn⟩
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact openCube_mono (innerRadius_bounds hR n).2.le hn

theorem locally_integrable_collision_invariant_unique {R : ℝ} (hR : 0<R)
    {f : E → ℝ} (hfl : LocallyIntegrableOn f (openCube R)) (hf : invariant R f) :
    ∃! b : Coefficients,
      f =ᵐ[(volume : Measure E).restrict (openCube R)] evaluate b := by
  obtain ⟨b,hb⟩ := locally_integrable_invariant_inner_cube (half_pos hR) (by linarith) hfl hf
  have hbe : f =ᵐ[(volume : Measure E).restrict (openCube (R/2))] evaluate b := hb
  have hn (n : ℕ) := locally_integrable_invariant_inner_cube
    (lt_of_lt_of_le (half_pos hR) (innerRadius_bounds hR n).1)
    (innerRadius_bounds hR n).2 hfl hf
  choose c hc using hn
  have hcoeff (n : ℕ) : b=c n := by
    have hcn := (hc n).filter_mono (ae_mono (Measure.restrict_mono_set volume
      (openCube_mono (innerRadius_bounds hR n).1)))
    exact coefficients_eq_of_ae (half_pos hR) (hbe.symm.trans hcn)
  have hglobal : f =ᵐ[(volume : Measure E).restrict (openCube R)] evaluate b := by
    rw [inner_cubes_exhaust hR]
    change ∀ᵐ x ∂(volume : Measure E).restrict (⋃n,openCube (innerRadius R n)), f x=evaluate b x
    rw [ae_restrict_iUnion_iff]
    intro n
    simpa only [← hcoeff n] using hc n
  refine ⟨b,hglobal,?_⟩
  intro a ha
  exact coefficients_eq_of_ae hR (ha.symm.trans hglobal)

end
end Resonance.FiveInvariantClassification
