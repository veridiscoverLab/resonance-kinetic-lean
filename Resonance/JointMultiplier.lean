import Resonance.FixedMultiplier
import Resonance.ResonantMeasure

/-!
Transfer convergence in volume to any of the four legs of the same concrete
joint pairing measure. A fixed test may depend on the entire quartet. No
independence of legs or moving-test convergence is assumed.
-/
namespace Resonance.JointMultiplier

open MeasureTheory Filter
open MeasureTheory.Measure
open scoped Topology BigOperators
open Resonance.ResonantMeasure

theorem pullback_tendstoInMeasure
    {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {σ : Measure β} [IsFiniteMeasure σ]
    {l : Filter ι} [l.IsCountablyGenerated]
    {T : β → α} (hT : QuasiMeasurePreserving T σ μ)
    {b : ι → α → ℝ} {c : α → ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) μ)
    (hconv : TendstoInMeasure μ b l c) :
    TendstoInMeasure σ (fun n x => b n (T x)) l (fun x => c (T x)) := by
  intro ε hε
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hlim⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hlimσ := hT.ae hlim
  have ht := tendstoInMeasure_of_tendsto_ae
    (fun n => (hb (ns (ms n))).comp_quasiMeasurePreserving hT) hlimσ
  exact ht ε hε

theorem leg_quasiMeasurePreserving (R : ℝ) (i : Fin 4) :
    QuasiMeasurePreserving (fun k : FourMomenta => k i) (pairingMeasure R) volume :=
  ⟨measurable_pi_apply i, pairing_marginal_absolutelyContinuous R i⟩

theorem leg_tendstoInMeasure {R : ℝ} (hR : 0 ≤ R)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (i : Fin 4) {b : ι → E → ℝ} {c : E → ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    (hconv : TendstoInMeasure volume b l c) :
    TendstoInMeasure (pairingMeasure R) (fun n k => b n (k i)) l (fun k => c (k i)) := by
  letI : IsFiniteMeasure (pairingMeasure R) := pairingMeasure_finite hR
  exact pullback_tendstoInMeasure (leg_quasiMeasurePreserving R i) hb hconv

/-- The fixed test V is a function of the complete four-leg configuration. -/
theorem joint_leg_multiplier_strong {R : ℝ} (hR : 0 ≤ R)
    {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} [l.IsCountablyGenerated] (i : Fin 4)
    {b : ι → E → ℝ} {c : E → ℝ} {V : FourMomenta → F} {C : ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    (hc : AEStronglyMeasurable c volume)
    (hbnd : ∀ n, ∀ᵐ x ∂volume, |b n x| ≤ C)
    (hcnd : ∀ᵐ x ∂volume, |c x| ≤ C)
    (hconv : TendstoInMeasure volume b l c)
    (hV : MemLp V 2 (pairingMeasure R)) :
    ∃ G : ι → Lp F 2 (pairingMeasure R),
      (∀ n, G n =ᵐ[pairingMeasure R] (fun k => (b n (k i)-c (k i)) • V k)) ∧
      Tendsto G l (𝓝 0) := by
  have hT := leg_quasiMeasurePreserving R i
  exact Resonance.FixedMultiplier.fixed_multiplier_strong
    (Measure.AbsolutelyContinuous.refl _) (leg_tendstoInMeasure hR i hb hconv)
    (fun n => (hb n).comp_quasiMeasurePreserving hT)
    (hc.comp_quasiMeasurePreserving hT)
    (fun n => hT.ae (hbnd n)) (hT.ae hcnd) hV


theorem leg_quasiMeasurePreserving_cube (R : ℝ) (i : Fin 4) :
    QuasiMeasurePreserving (fun k : FourMomenta => k i) (pairingMeasure R)
      (volume.restrict (cube R)) := by
  have hs : (pairingMeasure R).restrict (fullResonance R) = pairingMeasure R :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (pairing_supported_on_fullResonance R))
  have hm : Set.MapsTo (fun k : FourMomenta => k i) (fullResonance R) (cube R) :=
    fun k hk => hk.1 i
  have ht := (leg_quasiMeasurePreserving R i).restrict hm
  rwa [hs] at ht

theorem cube_leg_tendstoInMeasure {R : ℝ} (hR : 0 ≤ R)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (i : Fin 4) {b : ι → E → ℝ} {c : E → ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict (cube R)))
    (hconv : TendstoInMeasure (volume.restrict (cube R)) b l c) :
    TendstoInMeasure (pairingMeasure R) (fun n k => b n (k i)) l (fun k => c (k i)) := by
  letI : IsFiniteMeasure (pairingMeasure R) := pairingMeasure_finite hR
  exact pullback_tendstoInMeasure (leg_quasiMeasurePreserving_cube R i) hb hconv

/-- Only cube-a.e. data are needed; V may still depend on the entire quartet. -/
theorem cube_joint_leg_multiplier_strong {R : ℝ} (hR : 0 ≤ R)
    {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} [l.IsCountablyGenerated] (i : Fin 4)
    {b : ι → E → ℝ} {c : E → ℝ} {V : FourMomenta → F} {C : ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict (cube R)))
    (hc : AEStronglyMeasurable c (volume.restrict (cube R)))
    (hbnd : ∀ n, ∀ᵐ x ∂volume.restrict (cube R), |b n x| ≤ C)
    (hcnd : ∀ᵐ x ∂volume.restrict (cube R), |c x| ≤ C)
    (hconv : TendstoInMeasure (volume.restrict (cube R)) b l c)
    (hV : MemLp V 2 (pairingMeasure R)) :
    ∃ G : ι → Lp F 2 (pairingMeasure R),
      (∀ n, G n =ᵐ[pairingMeasure R] (fun k => (b n (k i)-c (k i)) • V k)) ∧
      Tendsto G l (𝓝 0) := by
  have hT := leg_quasiMeasurePreserving_cube R i
  exact Resonance.FixedMultiplier.fixed_multiplier_strong
    (Measure.AbsolutelyContinuous.refl _) (cube_leg_tendstoInMeasure hR i hb hconv)
    (fun n => (hb n).comp_quasiMeasurePreserving hT)
    (hc.comp_quasiMeasurePreserving hT)
    (fun n => hT.ae (hbnd n)) (hT.ae hcnd) hV


noncomputable def quartetRoot (b : E → ℝ) (k : FourMomenta) : ℝ :=
  Real.sqrt (∏ i : Fin 4, b (k i))

theorem quartetRoot_measurable (R : ℝ) {b : E → ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (cube R))) :
    AEStronglyMeasurable (quartetRoot b) (pairingMeasure R) := by
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  exact Finset.aestronglyMeasurable_fun_prod _ (fun i _ =>
    hb.comp_quasiMeasurePreserving (leg_quasiMeasurePreserving_cube R i))

theorem quartetRoot_tendstoInMeasure {R : ℝ} (hR : 0 ≤ R)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {b : ι → E → ℝ} {c : E → ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict (cube R)))
    (hconv : TendstoInMeasure (volume.restrict (cube R)) b l c) :
    TendstoInMeasure (pairingMeasure R) (fun n => quartetRoot (b n)) l (quartetRoot c) := by
  letI : IsFiniteMeasure (pairingMeasure R) := pairingMeasure_finite hR
  intro ε hε
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hlim⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hlegs : ∀ᵐ k ∂pairingMeasure R, ∀ i : Fin 4,
      Tendsto (fun n => b (ns (ms n)) (k i)) atTop (𝓝 (c (k i))) := by
    rw [ae_all_iff]
    intro i
    exact (leg_quasiMeasurePreserving_cube R i).ae hlim
  have hp : ∀ᵐ k ∂pairingMeasure R,
      Tendsto (fun n => quartetRoot (b (ns (ms n))) k) atTop (𝓝 (quartetRoot c k)) := by
    filter_upwards [hlegs] with k hk
    exact Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_finset_prod Finset.univ (fun i _ => hk i))
  exact (tendstoInMeasure_of_tendsto_ae
    (fun n => quartetRoot_measurable R (hb (ns (ms n)))) hp) ε hε

theorem quartetRoot_bound (R : ℝ) {b : E → ℝ} {C : ℝ}
    (hbnd : ∀ᵐ x ∂volume.restrict (cube R), |b x| ≤ C) :
    ∀ᵐ k ∂pairingMeasure R, |quartetRoot b k| ≤ C^2 := by
  have hlegs : ∀ᵐ k ∂pairingMeasure R, ∀ i : Fin 4, |b (k i)| ≤ C := by
    rw [ae_all_iff]
    intro i
    exact (leg_quasiMeasurePreserving_cube R i).ae hbnd
  filter_upwards [hlegs] with k hk
  have hprod : |∏ i : Fin 4, b (k i)| ≤ C^4 := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      abs_nonneg (b (k i))) (fun i _ => hk i)
  have hp : (∏ i : Fin 4, b (k i)) ≤ (C^2)^2 :=
    (le_abs_self _).trans (by nlinarith [hprod])
  change |Real.sqrt _| ≤ _
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg C)] using Real.sqrt_le_sqrt hp

/-- The complete square-root product multiplier used in the four-wave current.
This remains a fixed-test result; it does not assume strong convergence of a
moving microscopic vector. -/
theorem quartetRoot_fixed_test_strong {R : ℝ} (hR : 0 ≤ R)
    {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} [l.IsCountablyGenerated]
    {b : ι → E → ℝ} {c : E → ℝ} {V : FourMomenta → F} {C : ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict (cube R)))
    (hc : AEStronglyMeasurable c (volume.restrict (cube R)))
    (hbnd : ∀ n, ∀ᵐ x ∂volume.restrict (cube R), |b n x| ≤ C)
    (hcnd : ∀ᵐ x ∂volume.restrict (cube R), |c x| ≤ C)
    (hconv : TendstoInMeasure (volume.restrict (cube R)) b l c)
    (hV : MemLp V 2 (pairingMeasure R)) :
    ∃ G : ι → Lp F 2 (pairingMeasure R),
      (∀ n, G n =ᵐ[pairingMeasure R] (fun k =>
        (quartetRoot (b n) k-quartetRoot c k) • V k)) ∧ Tendsto G l (𝓝 0) := by
  exact Resonance.FixedMultiplier.fixed_multiplier_strong
    (Measure.AbsolutelyContinuous.refl _) (quartetRoot_tendstoInMeasure hR hb hconv)
    (fun n => quartetRoot_measurable R (hb n)) (quartetRoot_measurable R hc)
    (fun n => quartetRoot_bound R (hbnd n)) (quartetRoot_bound R hcnd) hV

end Resonance.JointMultiplier
