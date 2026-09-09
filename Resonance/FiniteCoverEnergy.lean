import Mathlib

/-! Finite-cover assembly for the full nonnegative collision error.
The hypotheses supply only an actual cover and local energy convergence;
global compactness or a spectral gap is never assumed. -/
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Resonance.FiniteCoverEnergy
noncomputable section

theorem restricted_measure_le_sum_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (T : Set X) (S : ι → Set X) (hcover : T ⊆ ⋃ i, S i) :
    μ.restrict T ≤ Measure.sum (fun i => μ.restrict (S i)) :=
  (Measure.restrict_mono_set μ hcover).trans Measure.restrict_iUnion_le

theorem lintegral_le_sum_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (T : Set X) (S : ι → Set X) (hcover : T ⊆ ⋃ i, S i)
    (F : X → ℝ≥0∞) :
    (∫⁻ x in T, F x ∂μ) ≤ ∑ i, ∫⁻ x in S i, F x ∂μ := by
  have hm := restricted_measure_le_sum_cover μ T S hcover
  apply (lintegral_mono' hm le_rfl).trans_eq
  rw [lintegral_sum_measure, tsum_fintype]

theorem tendsto_zero_of_finite_cover {X ι A : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (T : Set X) (S : ι → Set X) (hcover : T ⊆ ⋃ i, S i)
    (l : Filter A) (F : A → X → ℝ≥0∞)
    (hlocal : ∀ i, Tendsto (fun a => ∫⁻ x in S i, F a x ∂μ) l (𝓝 0)) :
    Tendsto (fun a => ∫⁻ x in T, F a x ∂μ) l (𝓝 0) := by
  have hs : Tendsto (fun a => ∑ i, ∫⁻ x in S i, F a x ∂μ) l (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ => hlocal i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ => zero_le _) (fun a => lintegral_le_sum_cover μ T S hcover (F a))

theorem squared_difference_energy_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (T : Set X) (S : ι → Set X) (hcover : T ⊆ ⋃ i, S i)
    (f : ℕ → X → ℂ)
    (hlocal : ∀ i, Tendsto
      (fun p : ℕ × ℕ => ∫⁻ x in S i, ‖f p.1 x-f p.2 x‖ₑ^2 ∂μ)
      (atTop ×ˢ atTop) (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫⁻ x in T, ‖f p.1 x-f p.2 x‖ₑ^2 ∂μ)
      (atTop ×ˢ atTop) (𝓝 0) :=
  tendsto_zero_of_finite_cover μ T S hcover _ _ hlocal

end
end Resonance.FiniteCoverEnergy
