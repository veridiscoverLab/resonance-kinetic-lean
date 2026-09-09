import Resonance.SpatialCollision
import Mathlib.Analysis.ODE.PicardLindelof

/-! Actual nonautonomous kinetic vector field in the free-transport frame.
All constants below are derived from the original four-wave fiber measure. -/
open Set Metric
open scoped NNReal

namespace Resonance.KineticField
noncomputable section
open FreeTransport SpatialCollision CollisionFiber TransportDuhamel

def field (R : ℝ) (hR : 0 ≤ R) (c t : ℝ) (g : Distribution R) : Distribution R :=
  c • transport R (-t) (collision R hR (transport R t g))

theorem field_joint_continuous (R : ℝ) (hR : 0 ≤ R) (c : ℝ) :
    Continuous (fun p : ℝ × Distribution R => field R hR c p.1 p.2) := by
  unfold field
  apply Continuous.const_smul
  exact (transport_joint_continuous R).comp (continuous_fst.neg.prodMk
    ((collision_continuous hR).comp (transport_joint_continuous R)))

theorem field_norm_le (R : ℝ) (hR : 0 ≤ R) (c t : ℝ) (g : Distribution R) :
    ‖field R hR c t g‖ ≤ |c| * (4 * ‖g‖^3 * (fiberMassBound R).toReal) := by
  unfold field
  rw [norm_smul, Real.norm_eq_abs, transport_norm]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  simpa only [transport_norm] using collision_norm_le R hR (transport R t g)

theorem field_sub_norm_le {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (c t : ℝ) (f g : Distribution R) (hf : ‖f‖ ≤ M) (hg : ‖g‖ ≤ M) :
    ‖field R hR c t f - field R hR c t g‖ ≤
      (|c| * (12 * M^2 * (fiberMassBound R).toReal)) * ‖f-g‖ := by
  unfold field
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have heq : transport R (-t) (collision R hR (transport R t f)) -
      transport R (-t) (collision R hR (transport R t g)) =
      transport R (-t) (collision R hR (transport R t f) -
        collision R hR (transport R t g)) :=
    ((transportCLM R (-t)).map_sub _ _).symm
  rw [heq, transport_norm]
  have hd : ‖transport R t f - transport R t g‖ = ‖f-g‖ := by
    change ‖transportCLM R t f - transportCLM R t g‖ = _
    rw [← map_sub]
    exact transport_norm R t (f-g)
  have h := collision_sub_norm_le hR hM (transport R t f) (transport R t g)
    (by simpa only [transport_norm] using hf) (by simpa only [transport_norm] using hg)
  rw [hd] at h
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg c)).trans_eq (mul_assoc _ _ _).symm

def sizeBound (R c : ℝ) (f₀ : Distribution R) (a : ℝ≥0) : ℝ≥0 :=
  ⟨|c| * (4 * (‖f₀‖ + a)^3 * (fiberMassBound R).toReal), by positivity⟩

def lipschitzBound (R c : ℝ) (f₀ : Distribution R) (a : ℝ≥0) : ℝ≥0 :=
  ⟨|c| * (12 * (‖f₀‖ + a)^2 * (fiberMassBound R).toReal), by positivity⟩

theorem norm_le_of_mem_ball {R : ℝ} (f₀ f : Distribution R) (a : ℝ≥0)
    (hf : f ∈ closedBall f₀ (a : ℝ)) : ‖f‖ ≤ ‖f₀‖ + a := by
  have hd : ‖f-f₀‖ ≤ a := by simpa [mem_closedBall, dist_eq_norm] using hf
  calc
    ‖f‖ ≤ ‖f-f₀‖ + ‖f₀‖ := norm_le_norm_sub_add f f₀
    _ ≤ _ := by linarith

theorem field_lipschitz_ball (R : ℝ) (hR : 0 ≤ R) (c t : ℝ)
    (f₀ : Distribution R) (a : ℝ≥0) :
    LipschitzOnWith (lipschitzBound R c f₀ a) (field R hR c t) (closedBall f₀ a) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro f hf g hg
  simpa only [dist_eq_norm, lipschitzBound, NNReal.coe_mk] using
    field_sub_norm_le hR (show 0 ≤ ‖f₀‖ + (a : ℝ) by positivity) c t f g
      (norm_le_of_mem_ball f₀ f a hf) (norm_le_of_mem_ball f₀ g a hg)

theorem field_size_ball (R : ℝ) (hR : 0 ≤ R) (c t : ℝ)
    (f₀ : Distribution R) (a : ℝ≥0) (f : Distribution R)
    (hf : f ∈ closedBall f₀ (a : ℝ)) :
    ‖field R hR c t f‖ ≤ sizeBound R c f₀ a := by
  apply (field_norm_le R hR c t f).trans
  change |c| * (4 * ‖f‖^3 * _) ≤ |c| * (4 * (‖f₀‖ + (a : ℝ))^3 * _)
  gcongr
  exact norm_le_of_mem_ball f₀ f a hf

/-- A positive local time determined by the actual amplitude and collision constant. -/
def localTime (R c : ℝ) (f₀ : Distribution R) (a : ℝ≥0) : ℝ :=
  (a : ℝ) / ((sizeBound R c f₀ a : ℝ) + 1)

theorem localTime_pos {R c : ℝ} (f₀ : Distribution R) {a : ℝ≥0} (ha : 0 < a) :
    0 < localTime R c f₀ a := by
  unfold localTime
  exact div_pos (by exact_mod_cast ha) (by positivity)

theorem localTime_size (R c : ℝ) (f₀ : Distribution R) (a : ℝ≥0) :
    (sizeBound R c f₀ a : ℝ) * localTime R c f₀ a ≤ a := by
  unfold localTime
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < (sizeBound R c f₀ a : ℝ) + 1)).mpr
  nlinarith [a.coe_nonneg]

theorem actual_picardLindelof (R : ℝ) (hR : 0 ≤ R) (c : ℝ)
    (f₀ : Distribution R) (a : ℝ≥0) (ha : 0 < a) :
    IsPicardLindelof (field R hR c)
      (⟨0, le_rfl, (localTime_pos f₀ ha).le⟩ : Icc 0 (localTime R c f₀ a))
      f₀ a 0 (sizeBound R c f₀ a) (lipschitzBound R c f₀ a) where
  lipschitzOnWith t _ := field_lipschitz_ball R hR c t f₀ a
  continuousOn f _ :=
    ((field_joint_continuous R hR c).comp (continuous_id.prodMk continuous_const)).continuousOn
  norm_le t _ f hf := field_size_ball R hR c t f₀ a f hf
  mul_max_le := by
    simp only [sub_zero, NNReal.coe_zero, max_eq_left (localTime_pos f₀ ha).le]
    exact localTime_size R c f₀ a

end
end Resonance.KineticField
