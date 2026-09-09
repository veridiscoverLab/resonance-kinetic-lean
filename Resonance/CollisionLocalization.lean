import Resonance.CollisionMollifierLimit
import Resonance.FreeTransport

/-! Localization and representative changes retain all four original sharp
flags and the same pairing measure. No regularity of the original representative
is assumed when transferring an almost-everywhere collision equation. -/
open Set MeasureTheory Filter
open scoped ENNReal

namespace Resonance.CollisionLocalization
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants CollisionMollifierLimit QuadraticPointwiseClosure

theorem cube_mono {r R : ℝ} (h : r ≤ R) : cube r ⊆ cube R := fun _ hx j => (hx j).trans h
theorem cube_subset_open {r R : ℝ} (h : r < R) : cube r ⊆ openCube R :=
  fun _ hx j => (hx j).trans_lt h
theorem openCube_mono {r R : ℝ} (h : r ≤ R) : openCube r ⊆ openCube R :=
  fun _ hx j => (hx j).trans_le h

theorem pairingMeasure_mono {r R : ℝ} (h : r ≤ R) : pairingMeasure r ≤ pairingMeasure R := by
  apply Measure.map_mono _ continuous_paired.measurable
  unfold parameterMeasure
  have ha : allowed r ⊆ allowed R := fun p hp i => cube_mono h (hp i)
  intro s
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_right ((Measure.restrict_mono_set base ha) s) 2

theorem invariant_mono {r R : ℝ} (h : r ≤ R) {f : E → ℝ} (hf : invariant R f) :
    invariant r f := hf.filter_mono (ae_mono (pairingMeasure_mono h))

theorem pairing_all_legs_ae (R : ℝ) : ∀ᵐ q ∂pairingMeasure R, ∀ i, q i ∈ cube R := by
  have hf : ∀ᵐ q ∂pairingMeasure R, q∈fullResonance R := by
    exact ae_iff.mpr (pairing_supported_on_fullResonance R)
  exact hf.mono (fun _ h => h.1)

theorem invariant_congr_on_cube {R : ℝ} {f g : E → ℝ}
    (hfg : EqOn f g (cube R)) (hf : invariant R f) : invariant R g := by
  filter_upwards [hf,pairing_all_legs_ae R] with q hq hflags
  simpa only [hfg (hflags 0),hfg (hflags 1),hfg (hflags 2),hfg (hflags 3)] using hq

theorem invariant_inner_representative {r R : ℝ} (hrR : r < R) {f g : E → ℝ}
    (hfg : f =ᵐ[(volume : Measure E).restrict (openCube R)] g) (hf : invariant R f) :
    invariant r g := by
  have hall : ∀ᵐ x ∂(volume : Measure E), x∈openCube R → f x=g x :=
    (ae_restrict_iff' (openCube_isOpen R).measurableSet).mp hfg
  have hleg (i : Fin 4) : ∀ᵐ q ∂pairingMeasure r,
      q i∈openCube R → f (q i)=g (q i) :=
    (show MeasureTheory.Measure.QuasiMeasurePreserving
      (fun q : FourMomenta => q i) (pairingMeasure r) volume from
      ⟨measurable_pi_apply i,pairing_marginal_absolutelyContinuous r i⟩).ae hall
  have he := ae_all_iff.mpr hleg
  filter_upwards [invariant_mono hrR.le hf,pairing_all_legs_ae r,he] with q hq hflags hEq
  have hi (i : Fin 4) := hEq i (cube_subset_open hrR (hflags i))
  simpa only [hi 0,hi 1,hi 2,hi 3] using hq

theorem locally_integrable_invariant_inner_cube {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {f : E → ℝ} (hfl : LocallyIntegrableOn f (openCube R)) (hf : invariant R f) :
    ∃ b : Coefficients, ∀ᵐ x ∂(volume : Measure E).restrict (openCube r), f x=evaluate b x := by
  let s := (r+R)/2
  have hrs : r<s := by dsimp [s]; linarith
  have hsR : s<R := by dsimp [s]; linarith
  let hm := hfl.aestronglyMeasurable
  let g := hm.mk f
  have hgm : Measurable g := hm.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[(volume : Measure E).restrict (openCube R)] g := hm.ae_eq_mk
  have hgl : LocallyIntegrableOn g (openCube R) := hfl.congr hfg
  have hgi : IntegrableOn g (cube s) :=
    hgl.integrableOn_compact_subset (cube_subset_open hsR) (FreeTransport.cube_isCompact s)
  let g₀ := (cube s).indicator g
  have hg₀m : Measurable g₀ := hgm.indicator (measurable_cube s)
  have hg₀i : Integrable g₀ := hgi.integrable_indicator (measurable_cube s)
  have hg₀f : invariant s g₀ := invariant_congr_on_cube
    (fun x hx => (Set.indicator_of_mem hx g).symm) (invariant_inner_representative hsR hfg hf)
  obtain ⟨b,hb⟩ := integrable_invariant_inner_cube hr hrs hg₀m hg₀i hg₀f
  refine ⟨b,?_⟩
  have hfg' := hfg.filter_mono (ae_mono (Measure.restrict_mono_set volume (openCube_mono hrR.le)))
  filter_upwards [hfg',hb,ae_restrict_mem (openCube_isOpen r).measurableSet] with x hx hxb hxr
  rw [hx]
  have hxs : x∈cube s := cube_mono hrs.le (openCube_subset_cube r hxr)
  simpa only [g₀,Set.indicator_of_mem hxs g] using hxb

end
end Resonance.CollisionLocalization
