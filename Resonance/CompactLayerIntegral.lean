import Resonance.EnergyCoordinateFubini
import Resonance.ShrinkingKernel

/-! Continuous compact source amplitudes give genuine continuous and integrable
energy readings. The mollifier may change shape arbitrarily. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CompactLayerIntegral
noncomputable section
open LinearSurfaceArea
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def layer (A : ℝ × P → E) (s : ℝ) : E := ∫x,A (s,x)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem slice_hasCompactSupport {A : ℝ × P → E} (hA : HasCompactSupport A) (s : ℝ) :
    HasCompactSupport (fun x => A (s,x)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hA.image continuous_snd)
  intro x hx
  exact ⟨(s,x),subset_tsupport A hx,rfl⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem slice_integrable {A : ℝ × P → E} (hc : Continuous A)
    (hA : HasCompactSupport A) (s : ℝ) : Integrable (fun x => A (s,x)) :=
  (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (slice_hasCompactSupport hA s)

omit [CompleteSpace E] in
theorem layer_continuous {A : ℝ × P → E} (hc : Continuous A)
    (hA : HasCompactSupport A) : Continuous (layer A) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (hA.image continuous_snd)
  · exact hc.continuousOn
  · intro s x _ hx
    by_contra hp
    exact hx ⟨(s,x),subset_tsupport A hp,rfl⟩

omit [CompleteSpace E] in
theorem layer_hasCompactSupport {A : ℝ × P → E} (hA : HasCompactSupport A) :
    HasCompactSupport (layer A) := by
  apply HasCompactSupport.of_support_subset_isCompact (hA.image continuous_fst)
  intro s hs
  by_contra hn
  apply hs
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_contra hp
  exact hn ⟨(s,x),subset_tsupport A hp,rfl⟩

omit [CompleteSpace E] in
theorem layer_integrable {A : ℝ × P → E} (hc : Continuous A)
    (hA : HasCompactSupport A) : Integrable (layer A) :=
  (layer_continuous hc hA).integrable_of_hasCompactSupport (layer_hasCompactSupport hA)

omit [CompleteSpace E] in
theorem weighted_joint_integrable {A : ℝ × P → E} (hc : Continuous A)
    (hA : HasCompactSupport A) {ρ : ℝ → ℝ} (hρ : Integrable ρ) :
    Integrable (fun p : ℝ × P => ρ p.1 • A p) := by
  let K := Prod.snd '' tsupport A
  have hK : IsCompact K := hA.image continuous_snd
  obtain ⟨C,hC⟩ := hA.exists_bound_of_continuous hc
  have hg : Integrable (K.indicator (fun _ : P => C)) :=
    (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const hK.measure_ne_top)
  apply (hρ.norm.mul_prod hg).mono'
    ((hρ.aestronglyMeasurable.comp_fst).smul hc.aestronglyMeasurable)
  filter_upwards [] with p
  by_cases hp : p.2∈K
  · rw [norm_smul,Real.norm_eq_abs,Set.indicator_of_mem hp]
    exact mul_le_mul_of_nonneg_left (hC p) (abs_nonneg _)
  · have hz : A p=0 := by
      by_contra hn
      exact hp ⟨p,subset_tsupport A hn,rfl⟩
    simp [hz,hp]

omit [CompleteSpace E] in
theorem weighted_joint_integral {A : ℝ × P → E} (hc : Continuous A)
    (hA : HasCompactSupport A) {ρ : ℝ → ℝ} (hρ : Integrable ρ) :
    ∫p:ℝ × P,ρ p.1 • A p = ∫s,ρ s • layer A s := by
  change ∫p:ℝ × P,ρ p.1 • A p ∂volume.prod volume=_
  rw [integral_prod _ (weighted_joint_integrable hc hA hρ)]
  congr 1
  ext s
  exact integral_smul (ρ s) (fun x => A (s,x))

theorem arbitrary_kernel_layer_tendsto {A : ℝ × P → E} (hc : Continuous A)
    (hA : HasCompactSupport A) (ρ : ℝ → ℝ → ℝ)
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀x,0≤ρ η x)
    (hmass : ∀η,0<η→∫x,ρ η x=1)
    (hsupport : ∀η,0<η→∀x,ρ η x≠0→|x|≤η) :
    Tendsto (fun η=>∫s,ρ η s • layer A s) (𝓝[>]0) (𝓝 (layer A 0)) :=
  ShrinkingKernel.arbitrary_kernel_tendsto ρ hρ hpos hmass hsupport
    (layer_continuous hc hA).aestronglyMeasurable (layer_continuous hc hA).continuousAt

end
end Resonance.CompactLayerIntegral
