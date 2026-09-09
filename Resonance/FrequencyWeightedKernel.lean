import Resonance.FrequencyWeightedForm
import Resonance.LocalSquareInvariants

/-! Local regularity and the exact five-dimensional kernel in the original
degenerating marginal space.  Compact sets stay inside the physical cube;
no global lower bound on the collision frequency is introduced. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.FrequencyWeightedKernel
noncomputable section
open ResonantMeasure WeightedJointMeasure CollisionMarginalDensity FrequencyWeightedForm
open CollisionFrequency CollisionFrequencyPositive ContinuousCollisionInvariants CollisionFiber

theorem profile_continuousOn {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) : ContinuousOn (profile θ) (cube R) :=
  (Entropy.cube_rj_continuousOn R θ hθ).comp coordinates_continuous.continuousOn
    (fun k hk=>(coordinates_cube R k).mp hk)

theorem profile_uniform_lower {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) : ∃m : ℝ, 0 < m ∧ ∀k∈cube R,m≤profile θ k := by
  have hne : (cube R).Nonempty := ⟨0,by simpa [cube] using hR⟩
  obtain ⟨k,hk,hmin⟩ := (FiberContinuity.cube_isCompact R).exists_isMinOn hne
    (profile_continuousOn hθ)
  exact ⟨profile θ k,profile_pos hθ hk,hmin⟩

theorem density_geometric_lower {R m : ℝ} (hR : 0≤R) (hm : 0 < m)
    {θ : Thermodynamics.Parameter} (hb : ∀k∈cube R,m≤profile θ k) (k : E) :
    ENNReal.ofReal (m^4*geometricFrequency R k)≤fiberDensity R (weight θ) k := by
  have hlow : ∀ᵐq∂fiberMeasure R k,ENNReal.ofReal (m^4)≤weight θ q := by
    filter_upwards [fiber_support R k] with q hq
    apply ENNReal.ofReal_le_ofReal
    change m^4≤∏i : Fin 4,profile θ (q i)
    calc
      _ = ∏_i : Fin 4,m := by simp
      _ ≤ _ := Finset.prod_le_prod (fun i _=>hm.le) (fun i _=>hb _ (hq.1 i))
  have hi := lintegral_mono_ae hlow
  simpa only [fiberDensity,lintegral_const,smul_eq_mul,geometricFrequency_eq_mass,
    ENNReal.ofReal_mul (by positivity : 0 ≤ m^4),
    ENNReal.ofReal_toReal (geometricFrequency_mass_finite hR k).ne] using hi

theorem compact_geometric_lower {R : ℝ} (hR : 0<R) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hsub : K⊆openCube R) :
    ∃b : ℝ,0<b ∧ ∀k∈K,b≤geometricFrequency R k := by
  have hc : ContinuousOn (geometricFrequency R) K :=
    (geometricFrequency_continuousOn hR.le).mono (fun k hk j=>(hsub hk j).le)
  obtain ⟨k,hk,hmin⟩ := hK.exists_isMinOn hne hc
  have hkc : k∈cube R := fun j=>(hsub hk j).le
  have hn : ¬isCubeCorner R k := fun h=>
    (ne_of_lt (hsub hk 0)) (h 0)
  exact ⟨geometricFrequency R k,geometricFrequency_noncorner_positive hR hkc hn,hmin⟩

theorem measure_le_density_lower {K : Set E} (hK : MeasurableSet K)
    {w : E→ℝ≥0∞} {a : ℝ} (ha : 0<a) (hl : ∀k∈K,ENNReal.ofReal a≤w k) :
    volume.restrict K≤(ENNReal.ofReal a)⁻¹ • volume.withDensity w := by
  have hm : ENNReal.ofReal a • volume.restrict K≤volume.withDensity w := by
    have hw : (K.indicator (fun _=>ENNReal.ofReal a))≤w := by
      intro k
      by_cases hk : k∈K
      · simpa [hk] using hl k hk
      · simp [hk]
    have h := withDensity_mono (μ := (volume : Measure E)) (Eventually.of_forall hw)
    rw [withDensity_indicator hK,withDensity_const] at h
    exact h
  have h : (ENNReal.ofReal a)⁻¹ • (ENNReal.ofReal a • volume.restrict K)≤
      (ENNReal.ofReal a)⁻¹ • volume.withDensity w := by
    intro s
    simpa only [Measure.smul_apply,smul_eq_mul] using
      mul_le_mul_right (hm s) ((ENNReal.ofReal a)⁻¹)
  simpa [smul_smul,ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr ha)
    ENNReal.ofReal_ne_top] using h

theorem compact_volume_dominated {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) {K : Set E}
    (hK : IsCompact K) (hsub : K⊆openCube R) :
    ∃C : ℝ≥0∞,C≠∞ ∧ volume.restrict K≤C • marginal R θ := by
  by_cases hne : K.Nonempty
  · obtain ⟨m,hm,hml⟩ := profile_uniform_lower hR.le hθ
    obtain ⟨b,hb,hbl⟩ := compact_geometric_lower hR hK hne hsub
    have ha : 0 < m^4*b := by positivity
    refine ⟨(ENNReal.ofReal (m^4*b))⁻¹,by simpa using ha,?_⟩
    rw [marginal,weighted_all_marginals hR.le θ 0]
    apply measure_le_density_lower hK.measurableSet ha
    intro k hk
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hbl k hk)
      (by positivity))).trans (density_geometric_lower hR.le hm hml k)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact ⟨0,by simp,by simp⟩

theorem marginal_L2_locally_square {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f : H R θ) :
    LocalSquareInvariants.LocalSquareIntegrableOn f (openCube R) := by
  intro K hsub hK
  obtain ⟨C,hC,hdom⟩ := compact_volume_dominated hR hθ hK hsub
  exact (Lp.memLp f).of_measure_le_smul hC hdom

theorem actual_weighted_kernel_unique {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f : H R θ) (hf : gram R θ f=0) :
    ∃!b : QuadraticPointwiseClosure.Coefficients,
      (f : E→ℝ)=ᵐ[volume.restrict (cube R)] QuadraticPointwiseClosure.evaluate b :=
  LocalSquareInvariants.original_real_L2local_classification hR
    (marginal_L2_locally_square hR hθ f) ((gram_zero_iff R hθ f).mp hf)

theorem actual_weighted_kernel_iff {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f : H R θ) :
    gram R θ f=0 ↔ ∃!b : QuadraticPointwiseClosure.Coefficients,
      (f : E→ℝ)=ᵐ[volume.restrict (cube R)] QuadraticPointwiseClosure.evaluate b := by
  constructor
  · exact actual_weighted_kernel_unique hR hθ f
  · rintro ⟨b,hb,_⟩
    apply (gram_zero_iff R hθ f).mpr
    exact WeightedFiveKernel.invariant_of_cube_ae_eq hb
      (WeightedFiveKernel.polynomial_invariant R b)

end
end Resonance.FrequencyWeightedKernel
