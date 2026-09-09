import Resonance.PhysicalMarginal

/-! The actual free-transport group on continuous functions over the original
spatial torus of period 2π and the closed sharp momentum cube. The momentum,
including its boundary and corners, is retained in every characteristic. -/
open Set

namespace Resonance.FreeTransport
noncomputable section
open ResonantMeasure

def period : ℝ := 2 * Real.pi
instance periodPositive : Fact (0 < period) := ⟨by unfold period; positivity⟩

abbrev SpatialTorus := Fin 3 → AddCircle period
abbrev MomentumDomain (R : ℝ) := {k : E // k ∈ cube R}
abbrev Phase (R : ℝ) := SpatialTorus × MomentumDomain R

theorem cube_isCompact (R : ℝ) : IsCompact (cube R) := by
  have hc : IsClosed (cube R) := by
    change IsClosed {k : E | ∀ j : Fin 3, |k j| ≤ R}
    simp only [setOf_forall]
    apply isClosed_iInter
    intro j
    exact isClosed_le (by fun_prop) continuous_const
  have hs : cube R ⊆ Metric.closedBall (0 : E) (3 * max R 0) := by
    intro k hk
    have hb := norm_le_three_R (le_max_right R 0) (fun j => (hk j).trans (le_max_left R 0))
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  exact (isCompact_closedBall (0 : E) (3 * max R 0)).of_isClosed_subset hc hs

instance momentumDomainCompact (R : ℝ) : CompactSpace (MomentumDomain R) :=
  isCompact_iff_compactSpace.mp (cube_isCompact R)

abbrev Distribution (R : ℝ) := C(Phase R, ℝ)

def characteristic {R : ℝ} (t : ℝ) (p : Phase R) : Phase R :=
  ((fun j => p.1 j - ((2 * t * (p.2 : E) j : ℝ) : AddCircle period)), p.2)

theorem characteristic_joint_continuous (R : ℝ) :
    Continuous (fun q : ℝ × Phase R => characteristic q.1 q.2) := by
  unfold characteristic
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    fun_prop
  · fun_prop

theorem characteristic_continuous (R : ℝ) (t : ℝ) :
    Continuous (characteristic (R := R) t) :=
  (characteristic_joint_continuous R).comp (continuous_const.prodMk continuous_id)

theorem characteristic_zero {R : ℝ} (p : Phase R) : characteristic 0 p = p := by
  apply Prod.ext
  · ext j
    simp [characteristic]
  · rfl

theorem characteristic_add {R : ℝ} (s t : ℝ) (p : Phase R) :
    characteristic s (characteristic t p) = characteristic (s+t) p := by
  apply Prod.ext
  · ext j
    change p.1 j - ((2*t*(p.2:E) j:ℝ):AddCircle period) -
      ((2*s*(p.2:E) j:ℝ):AddCircle period) =
      p.1 j - ((2*(s+t)*(p.2:E) j:ℝ):AddCircle period)
    rw [show 2*(s+t)*(p.2:E) j = 2*t*(p.2:E) j + 2*s*(p.2:E) j by ring,
      AddCircle.coe_add]
    abel
  · rfl

theorem characteristic_surjective (R : ℝ) (t : ℝ) :
    Function.Surjective (characteristic (R := R) t) := by
  intro p
  refine ⟨characteristic (-t) p, ?_⟩
  rw [characteristic_add, add_neg_cancel, characteristic_zero]

def transport (R : ℝ) (t : ℝ) (f : Distribution R) : Distribution R :=
  f.comp ⟨characteristic t, characteristic_continuous R t⟩

theorem transport_apply (R : ℝ) (t : ℝ) (f : Distribution R) (p : Phase R) :
    transport R t f p = f (characteristic t p) := rfl

theorem transport_zero (R : ℝ) (f : Distribution R) : transport R 0 f = f := by
  ext p
  rw [transport_apply, characteristic_zero]

theorem transport_add_time (R : ℝ) (s t : ℝ) (f : Distribution R) :
    transport R s (transport R t f) = transport R (s+t) f := by
  ext p
  simp only [transport_apply, characteristic_add, add_comm s t]

theorem transport_add (R : ℝ) (t : ℝ) (f g : Distribution R) :
    transport R t (f+g) = transport R t f + transport R t g := by ext p; rfl

theorem transport_smul (R : ℝ) (t a : ℝ) (f : Distribution R) :
    transport R t (a • f) = a • transport R t f := by ext p; rfl

theorem transport_norm_le (R : ℝ) (t : ℝ) (f : Distribution R) : ‖transport R t f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun p => f.norm_coe_le_norm (characteristic t p))

theorem transport_norm (R : ℝ) (t : ℝ) (f : Distribution R) : ‖transport R t f‖ = ‖f‖ := by
  apply le_antisymm (transport_norm_le R t f)
  apply (ContinuousMap.norm_le _ (norm_nonneg (transport R t f))).mpr
  intro p
  obtain ⟨q, rfl⟩ := characteristic_surjective R t p
  exact (transport R t f).norm_coe_le_norm q

def transportLinear (R : ℝ) (t : ℝ) : Distribution R →ₗ[ℝ] Distribution R where
  toFun := transport R t
  map_add' := transport_add R t
  map_smul' := transport_smul R t

def transportIsometry (R : ℝ) (t : ℝ) : Distribution R →ₗᵢ[ℝ] Distribution R where
  toLinearMap := transportLinear R t
  norm_map' := transport_norm R t

def transportCLM (R : ℝ) (t : ℝ) : Distribution R →L[ℝ] Distribution R :=
  (transportIsometry R t).toContinuousLinearMap

theorem transport_strong_continuous (R : ℝ) (f : Distribution R) :
    Continuous (fun t : ℝ => transport R t f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (characteristic_joint_continuous R)

theorem transport_preserves_nonneg (R : ℝ) (t : ℝ) (f : Distribution R)
    (hf : ∀ p, 0 ≤ f p) : ∀ p, 0 ≤ transport R t f p := fun p => hf (characteristic t p)

theorem transport_preserves_interval (R : ℝ) (t m M : ℝ) (f : Distribution R)
    (hf : ∀ p, m ≤ f p ∧ f p ≤ M) : ∀ p, m ≤ transport R t f p ∧ transport R t f p ≤ M :=
  fun p => hf (characteristic t p)

end
end Resonance.FreeTransport
