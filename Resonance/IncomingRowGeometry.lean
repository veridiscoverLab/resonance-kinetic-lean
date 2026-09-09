import Resonance.SphereLatitudeNull
import Resonance.IncomingPairDensity

/-! Moving sharp flags in the true incoming-pair sphere.  The output
leg is kept inside the original cube; both outgoing faces are null for
every nonzero incoming separation. -/
open MeasureTheory Set Filter Real Metric
open scoped ENNReal Topology
namespace Resonance.IncomingRowGeometry
noncomputable section
set_option maxHeartbeats 600000
open ResonantMeasure IncomingPairMarginal FiberContinuity

theorem incomingQuartet_continuous : Continuous incomingQuartet := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [incomingQuartet] <;> fun_prop

theorem incoming_outgoing_level_null {k p : E} (hkp : k ≠ p)
    (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) (j : Fin 3) (a : ℝ) :
    surface {σ : Sphere | incomingQuartet ((k,p),σ) i j = a} = 0 := by
  have hr : ‖k-p‖/2 ≠ 0 := div_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hkp)) (by norm_num)
  fin_cases i
  · exact False.elim (hi0 rfl)
  · exact False.elim (hi1 rfl)
  · apply measure_mono_null (t := {σ : Sphere | (σ:E) j =
        (a-(1/2:ℝ)*(k j+p j))/(‖k-p‖/2)})
    · intro σ hσ
      change (1/2:ℝ)*(k j+p j)+(‖k-p‖/2)*(σ:E) j=a at hσ
      change (σ:E) j = _
      apply (eq_div_iff hr).mpr
      nlinarith
    · exact SphereLatitudeNull.sphere_coordinate_level_null j _
  · apply measure_mono_null (t := {σ : Sphere | (σ:E) j =
        ((1/2:ℝ)*(k j+p j)-a)/(‖k-p‖/2)})
    · intro σ hσ
      change (1/2:ℝ)*(k j+p j)-(‖k-p‖/2)*(σ:E) j=a at hσ
      change (σ:E) j = _
      apply (eq_div_iff hr).mpr
      nlinarith
    · exact SphereLatitudeNull.sphere_coordinate_level_null j _

theorem incoming_outgoing_faces_avoided {k p : E} (hkp : k ≠ p) (R : ℝ) :
    ∀ᵐ σ ∂surface, ∀ i : Fin 4, i ≠ 0 → i ≠ 1 → ∀ j : Fin 3,
      |incomingQuartet ((k,p),σ) i j| ≠ R := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi0 : i=0
  · exact ae_of_all _ (fun _ h => False.elim (h hi0))
  by_cases hi1 : i=1
  · exact ae_of_all _ (fun _ _ h => False.elim (h hi1))
  have h : ∀ᵐ σ ∂surface, ∀ j : Fin 3,
      incomingQuartet ((k,p),σ) i j ≠ R ∧ incomingQuartet ((k,p),σ) i j ≠ -R := by
    apply ae_all_iff.mpr
    intro j
    have hp := (measure_eq_zero_iff_ae_notMem.mp (incoming_outgoing_level_null hkp i hi0 hi1 j R))
    have hm := (measure_eq_zero_iff_ae_notMem.mp (incoming_outgoing_level_null hkp i hi0 hi1 j (-R)))
    filter_upwards [hp,hm] with σ hp hm
    exact ⟨hp,hm⟩
  filter_upwards [h] with σ hσ _ _ j
  intro habs
  rcases le_total 0 (incomingQuartet ((k,p),σ) i j) with hn | hn
  · exact (hσ j).1 (by rwa [abs_of_nonneg hn] at habs)
  · exact (hσ j).2 (by rw [abs_of_nonpos hn] at habs; linarith)

theorem incomingSharp_continuousWithinAt (R : ℝ) (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    {k p : E} (hk : k ∈ cube R) (σ : Sphere)
    (hσ : ∀ i : Fin 4, i ≠ 0 → i ≠ 1 → ∀ j : Fin 3,
      |incomingQuartet ((k,p),σ) i j| ≠ R) :
    ContinuousWithinAt (fun a : E => CoareaNormalization.sharpReadout R Φ
      (incomingQuartet ((a,p),σ))) (cube R) k := by
  have hc : Continuous (fun a : E => incomingQuartet ((a,p),σ)) :=
    incomingQuartet_continuous.comp (by fun_prop)
  have hcoords : ∀ᶠ a in 𝓝 k, ∀ i : Fin 4, i ≠ 0 → i ≠ 1 → ∀ j : Fin 3,
      (|incomingQuartet ((a,p),σ) i j| ≤ R ↔ |incomingQuartet ((k,p),σ) i j| ≤ R) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi0 : i=0
    · exact Eventually.of_forall (fun _ h => False.elim (h hi0))
    by_cases hi1 : i=1
    · exact Eventually.of_forall (fun _ _ h => False.elim (h hi1))
    apply Filter.Eventually.mono ?_ (fun _ h _ _ => h)
    apply Filter.eventually_all.mpr
    intro j
    have hj : Continuous (fun q : FourMomenta => |q i j|) := by fun_prop
    exact coordinate_threshold_eventually (hj.comp hc).continuousAt (hσ i hi0 hi1 j)
  have hflags : ∀ᶠ a in nhdsWithin k (cube R),
      (incomingQuartet ((a,p),σ) ∈ CoareaNormalization.allFourFlags R ↔
        incomingQuartet ((k,p),σ) ∈ CoareaNormalization.allFourFlags R) := by
    filter_upwards [hcoords.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with a ha hacube
    change (∀ i, ∀ j, |incomingQuartet ((a,p),σ) i j| ≤ R) ↔
      (∀ i, ∀ j, |incomingQuartet ((k,p),σ) i j| ≤ R)
    apply forall_congr'
    intro i
    by_cases hi0 : i=0
    · subst i
      exact iff_of_true hacube hk
    by_cases hi1 : i=1
    · subst i
      rfl
    · exact forall_congr' (fun j => ha i hi0 hi1 j)
  by_cases h0 : incomingQuartet ((k,p),σ) ∈ CoareaNormalization.allFourFlags R
  · have heq : (fun a : E => CoareaNormalization.sharpReadout R Φ (incomingQuartet ((a,p),σ)))
        =ᶠ[nhdsWithin k (cube R)] (fun a => Φ (incomingQuartet ((a,p),σ))) := by
      filter_upwards [hflags] with a ha
      exact Set.indicator_of_mem (ha.mpr h0) Φ
    change Tendsto _ _ (𝓝 (CoareaNormalization.sharpReadout R Φ (incomingQuartet ((k,p),σ))))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem h0]
    exact (hΦ.comp hc).continuousWithinAt.tendsto.congr' heq.symm
  · have heq : (fun a : E => CoareaNormalization.sharpReadout R Φ (incomingQuartet ((a,p),σ)))
        =ᶠ[nhdsWithin k (cube R)] (fun _ => (0:ℝ)) := by
      filter_upwards [hflags] with a ha
      exact Set.indicator_of_notMem (fun h => h0 (ha.mp h)) Φ
    change Tendsto _ _ (𝓝 (CoareaNormalization.sharpReadout R Φ (incomingQuartet ((k,p),σ))))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem h0]
    exact tendsto_const_nhds.congr' heq.symm

end
end Resonance.IncomingRowGeometry
