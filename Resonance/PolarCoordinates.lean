import Resonance.CoareaNormalization

/-! Exact nine-dimensional volume and double polar-coordinate bridges for the
same complete four-leg energy layer.  No coarea identity is assumed. -/
open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Resonance.PolarCoordinates
noncomputable section

open ResonantMeasure CoareaNormalization
abbrev E := ResonantMeasure.E

def curryNine : Nine ≃ᵐ (Fin 3 → Fin 3 → ℝ) :=
  MeasurableEquiv.curry (Fin 3) (Fin 3) ℝ

theorem curryNine_preserves_volume : MeasurePreserving curryNine volume volume := by
  apply MeasurePreserving.symm curryNine.symm
  refine ⟨curryNine.symm.measurable, ?_⟩
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : curryNine.symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i : Fin 3 => Set.univ.pi (fun j : Fin 3 => s (i,j))) := by
    ext x
    simp [curryNine, Set.mem_pi, Function.uncurry, Prod.forall]
  rw [he]
  change (Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))))
    (Set.univ.pi (fun i : Fin 3 => Set.univ.pi (fun j : Fin 3 => s (i,j)))) = _
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : Fin 3 × Fin 3 => (volume : Measure ℝ) (s p))).symm

def splitThree : (Fin 3 → E) ≃ᵐ (E × (E × E)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => E) 0).trans
    ((MeasurableEquiv.refl E).prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => E)))

theorem splitThree_apply (f : Fin 3 → E) : splitThree f = (f 0, f 1, f 2) := by
  rfl

theorem splitThree_preserves_volume : MeasurePreserving splitThree volume volume := by
  exact ((MeasurePreserving.id (volume : Measure E)).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => E))).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => E) 0)

def nineToTriple (z : Nine) : E × (E × E) :=
  (momentumAt z 0, momentumAt z 1, momentumAt z 2)

theorem nineToTriple_preserves_volume :
    MeasurePreserving nineToTriple (volume : Measure Nine)
      ((volume : Measure E).prod (volume.prod volume)) := by
  have hp := volume_preserving_pi (fun _ : Fin 3 => PiLp.volume_preserving_toLp (Fin 3))
  exact splitThree_preserves_volume.comp (hp.comp curryNine_preserves_volume)

def polarVector (p : Sphere × Radius) : E := (p.2 : ℝ) • (p.1 : E)

theorem polarVector_preserves_volume :
    MeasurePreserving polarVector (surface.prod (Measure.volumeIoiPow 2)) volume := by
  have hc : MeasurePreserving (Subtype.val : ({(0 : E)}ᶜ : Set E) → E)
      ((volume : Measure E).comap Subtype.val) volume := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_singleton _).compl,
      restrict_compl_singleton]
  have hh := MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    euclidean_polar_coordinates
  exact hc.comp hh

def polarBase : Measure Parameters :=
  (volume : Measure E).prod
    ((Measure.volumeIoiPow 2).prod (surface.prod surface))

instance : SigmaFinite polarBase := by unfold polarBase; infer_instance

theorem polarVector_integral (F : E → ℝ) (hF : AEStronglyMeasurable F volume) :
    (∫ k, F k) = ∫ p, F (polarVector p) ∂(surface.prod (Measure.volumeIoiPow 2)) := by
  have he := integral_map polarVector_preserves_volume.measurable.aemeasurable
    (polarVector_preserves_volume.map_eq.symm ▸ hF)
  rw [polarVector_preserves_volume.map_eq] at he
  exact he

theorem radial_three_from_two :
    Measure.volumeIoiPow 3 =
      (Measure.volumeIoiPow 2).withDensity (fun r : Radius => ENNReal.ofReal (r : ℝ)) := by
  unfold Measure.volumeIoiPow
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext r
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1

theorem base_from_polarBase :
    base = polarBase.withDensity (fun p : Parameters => ENNReal.ofReal (p.2.1 : ℝ)) := by
  rw [base, radial, radial_three_from_two,
    prod_withDensity_left (by fun_prop),
    prod_withDensity_right (by fun_prop)]
  rfl

def doublePolar (q : Parameters × Radius) : E × (E × E) :=
  (q.1.1, (q.1.2.1 : ℝ) • (q.1.2.2.1 : E), (q.2 : ℝ) • (q.1.2.2.2 : E))

theorem doublePolar_preserves_volume :
    MeasurePreserving doublePolar (polarBase.prod (Measure.volumeIoiPow 2))
      ((volume : Measure E).prod (volume.prod volume)) := by
  let m := Measure.volumeIoiPow 2
  letI : SigmaFinite m := inferInstanceAs (SigmaFinite (Measure.volumeIoiPow 2))
  letI : SigmaFinite (surface.prod m) := inferInstance
  letI : SigmaFinite (surface.prod (surface.prod m)) := inferInstance
  letI : SigmaFinite (m.prod (surface.prod (surface.prod m))) := inferInstance
  letI : SigmaFinite ((m.prod surface).prod (surface.prod m)) := inferInstance
  have h₁ := measurePreserving_prodAssoc (volume : Measure E)
    (m.prod (surface.prod surface)) m
  have h₂ := (MeasurePreserving.id (volume : Measure E)).prod
    (measurePreserving_prodAssoc m (surface.prod surface) m)
  have h₃ := (MeasurePreserving.id (volume : Measure E)).prod
    ((MeasurePreserving.id m).prod (measurePreserving_prodAssoc surface surface m))
  have h₄ := (MeasurePreserving.id (volume : Measure E)).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc m surface (surface.prod m)))
  have h₅ := (MeasurePreserving.id (volume : Measure E)).prod
    ((polarVector_preserves_volume.comp Measure.measurePreserving_swap).prod
      polarVector_preserves_volume)
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

theorem doublePolar_integrable (F : E × (E × E) → ℝ)
    (hF : Integrable F ((volume : Measure E).prod (volume.prod volume))) :
    Integrable (fun q => F (doublePolar q)) (polarBase.prod (Measure.volumeIoiPow 2)) :=
  doublePolar_preserves_volume.integrable_comp_of_integrable hF

theorem nine_doublePolar_integral (F : E × (E × E) → ℝ)
    (hF : Integrable F ((volume : Measure E).prod (volume.prod volume))) :
    (∫ z : Nine, F (nineToTriple z)) =
      ∫ p, ∫ s : Radius, F (doublePolar (p,s)) ∂(Measure.volumeIoiPow 2) ∂polarBase := by
  have hN := integral_map nineToTriple_preserves_volume.measurable.aemeasurable
    (nineToTriple_preserves_volume.map_eq.symm ▸ hF.aestronglyMeasurable)
  rw [nineToTriple_preserves_volume.map_eq] at hN
  have hP := integral_map doublePolar_preserves_volume.measurable.aemeasurable
    (doublePolar_preserves_volume.map_eq.symm ▸ hF.aestronglyMeasurable)
  rw [doublePolar_preserves_volume.map_eq] at hP
  exact hN.symm.trans (hP.trans (integral_prod _ (doublePolar_integrable F hF)))

theorem radial_two_integral (F : ℝ → ℝ) :
    (∫ r : Radius, F r ∂(Measure.volumeIoiPow 2)) = ∫ s in Ioi 0, s ^ 2 * F s := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  exact integral_subtype_comap measurableSet_Ioi (fun s => s ^ 2 * F s)

theorem base_integral (F : Parameters → ℝ) :
    (∫ p, F p ∂base) = ∫ p, (p.2.1 : ℝ) * F p ∂polarBase := by
  rw [base_from_polarBase, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    rw [ENNReal.toReal_ofReal p.2.1.property.le, smul_eq_mul])

theorem pairing_integral (R : ℝ) (Φ : ResonantMeasure.FourMomenta → ℝ)
    (hΦ : Measurable Φ) :
    (∫ k, Φ k ∂pairingMeasure R) =
      2 * ∫ p, (p.2.1 : ℝ) * (allowed R).indicator (fun p => Φ (paired p)) p ∂polarBase := by
  rw [pairingMeasure, integral_map continuous_paired.measurable.aemeasurable
    hΦ.aestronglyMeasurable, parameterMeasure, integral_smul_measure]
  norm_num
  rw [← integral_indicator (measurable_allowed R), base_integral]

theorem doublePolar_integrable_iff (F : E × (E × E) → ℝ)
    (hF : AEStronglyMeasurable F ((volume : Measure E).prod (volume.prod volume))) :
    Integrable (fun q => F (doublePolar q)) (polarBase.prod (Measure.volumeIoiPow 2)) ↔
      Integrable F ((volume : Measure E).prod (volume.prod volume)) :=
  doublePolar_preserves_volume.integrable_comp hF

theorem nineToTriple_integrable_iff (F : E × (E × E) → ℝ)
    (hF : AEStronglyMeasurable F ((volume : Measure E).prod (volume.prod volume))) :
    Integrable (fun z => F (nineToTriple z)) (volume : Measure Nine) ↔
      Integrable F ((volume : Measure E).prod (volume.prod volume)) :=
  nineToTriple_preserves_volume.integrable_comp hF

def tripleFour (t : E × (E × E)) : ResonantMeasure.FourMomenta :=
  ![t.1 + t.2.1, t.1 - t.2.1, t.1 + t.2.2, t.1 - t.2.2]

theorem tripleFour_nine (z : Nine) : tripleFour (nineToTriple z) = pairedFour z := rfl

theorem tripleFour_doublePolar (p : Parameters) (s : Radius) :
    tripleFour (doublePolar (p,s)) = radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2 := rfl

theorem complete_four_leg_doublePolar_integral (Φ : ResonantMeasure.FourMomenta → ℝ)
    (hΦ : Integrable (fun t => Φ (tripleFour t))
      ((volume : Measure E).prod (volume.prod volume))) :
    (∫ z : Nine, Φ (pairedFour z)) =
      ∫ p, (∫ s in Ioi 0, s ^ 2 *
        Φ (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2)) ∂polarBase := by
  change (∫ z : Nine, Φ (tripleFour (nineToTriple z))) = _
  rw [nine_doublePolar_integral (fun t => Φ (tripleFour t)) hΦ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p =>
    radial_two_integral (fun s => Φ (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2)))

theorem boxKernel_measurable : Measurable boxKernel :=
  measurable_const.indicator measurableSet_Icc

theorem boxKernel_norm_le (e : ℝ) : ‖boxKernel e‖ ≤ 1 / 2 := by
  by_cases he : e ∈ Icc (-1 : ℝ) 1 <;> norm_num [boxKernel, he]

theorem continuous_four_flags_bound {R : ℝ} (hR : 0 ≤ R)
    (Φ : ResonantMeasure.FourMomenta → ℝ) (hΦ : Continuous Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ allFourFlags R, ‖Φ k‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ResonantMeasure.FourMomenta) (3 * R)).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro k hk
  apply (hB k ?_).trans (le_max_left B 0)
  rw [mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * R)).mpr
    (fun i => norm_le_three_R hR (hk i))

def sharpLayer (R c : ℝ) (Φ : ResonantMeasure.FourMomenta → ℝ)
    (k : ResonantMeasure.FourMomenta) : ℝ :=
  sharpReadout R Φ k * (c * boxKernel (c * energy k))

theorem sharpLayer_measurable (R c : ℝ) {Φ : ResonantMeasure.FourMomenta → ℝ}
    (hΦ : Measurable Φ) : Measurable (sharpLayer R c Φ) :=
  (sharpReadout_measurable R hΦ).mul
    (measurable_const.mul (boxKernel_measurable.comp
      (measurable_const.mul energy_continuous.measurable)))

/-- A concrete compact-support criterion; the applications below derive its
support premise from all four original cube flags. -/
theorem sharpLayer_integrable_of_compact
    {A : Type*} [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (R c : ℝ) (Φ : ResonantMeasure.FourMomenta → ℝ) (hΦ : Continuous Φ)
    (F : A → ResonantMeasure.FourMomenta) (hF : Continuous F)
    (K : Set A) (hK : IsCompact K) (hflag : ∀ a, F a ∈ allFourFlags R → a ∈ K) :
    Integrable (fun a => sharpLayer R c Φ (F a)) μ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hΦ.comp hF).continuousOn
  have hm : AEStronglyMeasurable (fun a => sharpLayer R c Φ (F a)) μ :=
    ((sharpLayer_measurable R c hΦ.measurable).comp hF.measurable).aestronglyMeasurable
  have hbound (a : A) : ‖sharpLayer R c Φ (F a)‖ ≤ max B 0 * (‖c‖ / 2) := by
    by_cases ha : F a ∈ allFourFlags R
    · have hb := (hB a (hflag a ha)).trans (le_max_left B 0)
      change ‖sharpReadout R Φ (F a) * (c * boxKernel (c * energy (F a)))‖ ≤ _
      rw [sharpReadout, indicator_of_mem ha, norm_mul, norm_mul]
      calc
        _ ≤ max B 0 * (‖c‖ * (1 / 2)) := by
          gcongr
          exact hb
          exact boxKernel_norm_le _
        _ = _ := by ring
    · simp only [sharpLayer, sharpReadout, indicator_of_notMem ha, zero_mul, norm_zero]
      positivity
  have hi : IntegrableOn (fun a => sharpLayer R c Φ (F a)) K μ :=
    IntegrableOn.of_bound hK.measure_lt_top hm.restrict _ (Filter.Eventually.of_forall hbound)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro a ha
  have hf : F a ∉ allFourFlags R := fun h => ha (hflag a h)
  simp [sharpLayer, sharpReadout, hf]

theorem physical_flags_bound {R : ℝ} (hR : 0 ≤ R) {z : Nine}
    (hz : physicalFour z ∈ allFourFlags R) : ‖z‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  rintro ⟨i,j⟩
  have h (i : Fin 3) : |z (i,j)| ≤ R := by
    fin_cases i
    · exact hz 0 j
    · exact hz 1 j
    · exact hz 2 j
  exact h i

theorem original_sharp_layer_integrable {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : ResonantMeasure.FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Integrable (fun z : Nine => sharpLayer R c Φ (physicalFour z)) volume := by
  apply sharpLayer_integrable_of_compact volume R c Φ hΦ physicalFour physicalFour_continuous
    (closedBall 0 R) (isCompact_closedBall _ _)
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using physical_flags_bound hR hz

theorem tripleFour_continuous : Continuous tripleFour := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [tripleFour] <;> fun_prop

theorem triple_flags_bound {R : ℝ} (hR : 0 ≤ R) {t : E × (E × E)}
    (ht : tripleFour t ∈ allFourFlags R) : ‖t‖ ≤ 3 * R := by
  have h0 := norm_le_three_R hR (ht 0)
  have h1 := norm_le_three_R hR (ht 1)
  have h2 := norm_le_three_R hR (ht 2)
  have h3 := norm_le_three_R hR (ht 3)
  have hv := norm_add_le (tripleFour t 0) (tripleFour t 1)
  have hp := norm_sub_le (tripleFour t 0) (tripleFour t 1)
  have hq := norm_sub_le (tripleFour t 2) (tripleFour t 3)
  have ev : tripleFour t 0 + tripleFour t 1 = (2 : ℝ) • t.1 := by simp [tripleFour, two_smul]
  have ep : tripleFour t 0 - tripleFour t 1 = (2 : ℝ) • t.2.1 := by
    simp [tripleFour, two_smul]
  have eq : tripleFour t 2 - tripleFour t 3 = (2 : ℝ) • t.2.2 := by
    simp [tripleFour, two_smul]
  rw [ev, norm_smul] at hv
  rw [ep, norm_smul] at hp
  rw [eq, norm_smul] at hq
  norm_num at hv hp hq
  rw [Prod.norm_def, Prod.norm_def, max_le_iff, max_le_iff]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem triple_sharp_layer_integrable {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : ResonantMeasure.FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Integrable (fun t => sharpLayer R c Φ (tripleFour t))
      ((volume : Measure E).prod (volume.prod volume)) := by
  apply sharpLayer_integrable_of_compact volume R c Φ hΦ tripleFour tripleFour_continuous
    (closedBall 0 (3 * R)) (isCompact_closedBall _ _)
  intro t ht
  simpa only [mem_closedBall, dist_zero_right] using triple_flags_bound hR ht

theorem raw_joint_layer_integrable {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : ResonantMeasure.FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Integrable (fun q : Parameters × Radius => sharpLayer R c Φ
      (radialFour q.1.1 q.1.2.1 q.1.2.2.1 q.2 q.1.2.2.2))
      (polarBase.prod (Measure.volumeIoiPow 2)) :=
  doublePolar_integrable _ (triple_sharp_layer_integrable hR c Φ hΦ)

theorem original_sharp_layer_doublePolar {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : ResonantMeasure.FourMomenta → ℝ) (hΦ : Continuous Φ) :
    (∫ z : Nine, sharpLayer R c Φ (physicalFour z)) =
      8 * ∫ p, (∫ s in Ioi 0, s ^ 2 * sharpReadout R Φ
        (radialFour p.1 p.2.1 p.2.2.1 s p.2.2.2) *
        (c * boxKernel (c * radialEnergy p.2.1 s))) ∂polarBase := by
  rw [four_leg_integral_change _
    (original_sharp_layer_integrable hR c Φ hΦ).aestronglyMeasurable,
    complete_four_leg_doublePolar_integral _ (triple_sharp_layer_integrable hR c Φ hΦ)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    simp only [sharpLayer, radialFour_energy]
    ring)

end
end Resonance.PolarCoordinates
