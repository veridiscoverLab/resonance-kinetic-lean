import Resonance.PinnedPeriodicity

/-! Quantitative localization of the same periodic regular coarea.
A compact portion of the real lift meets only finitely many original winding
cells; every translated cell has exactly the original quotient measure. -/
open Real MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace Resonance.PinnedCompactLocalization
noncomputable section
open PinnedMeasure PinnedPeriodicity

def translation (n : Fin 3 → ℤ) : Ambient ≃ᵢ Ambient :=
  IsometryEquiv.addRight (latticeShift n)

theorem translation_apply (n : Fin 3 → ℤ) (k : Ambient) :
    translation n k = k + latticeShift n := rfl

theorem coareaWeight_lattice (d : ℝ) (n : Fin 3 → ℤ) (k : Ambient) :
    coareaWeight d (translation n k) = coareaWeight d k := by
  simp only [coareaWeight, translation_apply, energyGradient_lattice]

theorem coarea_translation_preserving {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (n : Fin 3 → ℤ) :
    MeasurePreserving (translation n) (liftedRegularCoarea d) (liftedRegularCoarea d) := by
  have hpre : translation n ⁻¹' regularSurface d = regularSurface d := by
    ext k
    exact regularSurface_lattice d n k
  have hraw : MeasurePreserving (translation n)
      ((μH[2] : Measure Ambient).restrict (regularSurface d))
      ((μH[2] : Measure Ambient).restrict (regularSurface d)) := by
    simpa only [hpre] using
      ((translation n).measurePreserving_hausdorffMeasure 2).restrict_preimage
        (regularSurface_measurable hd0 hdU)
  refine ⟨(translation n).continuous.measurable, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (translation n).continuous.measurable hA,
    liftedRegularCoarea, withDensity_apply _ (hA.preimage (translation n).continuous.measurable),
    withDensity_apply _ hA]
  have he := hraw.setLIntegral_comp_preimage hA (coareaWeight_measurable hd0 hdU)
  simpa only [coareaWeight_lattice] using he

def translatedCell (n : Fin 3 → ℤ) : Set Ambient := translation n '' fundamentalCell

theorem translatedCell_measurable (n : Fin 3 → ℤ) : MeasurableSet (translatedCell n) :=
  (translation n).toHomeomorph.measurableEmbedding.measurableSet_image.mpr fundamentalCell_measurable

theorem cell_translation_preserving {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (n : Fin 3 → ℤ) : MeasurePreserving (translation n) (cellCoarea d)
      ((liftedRegularCoarea d).restrict (translatedCell n)) := by
  have hp := (coarea_translation_preserving hd0 hdU n).restrict_preimage
    (translatedCell_measurable n)
  simpa only [translatedCell, (translation n).injective.preimage_image] using hp

theorem quotient_translation (n : Fin 3 → ℤ) (k : Ambient) :
    quotientCoordinates (translation n k) = quotientCoordinates k := by
  ext i
  exact periodic_coordinate (f := fun x : ℝ => (x : PinnedPeriodicity.Circle))
    (by intro x; simp) n k i

theorem translatedCell_quotient_measure {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (n : Fin 3 → ℤ) :
    ((liftedRegularCoarea d).restrict (translatedCell n)).map quotientCoordinates =
      circleRegularCoarea d := by
  rw [← (cell_translation_preserving hd0 hdU n).map_eq,
    Measure.map_map quotientCoordinates_continuous.measurable (translation n).continuous.measurable]
  congr 1
  funext k
  exact quotient_translation n k

theorem compact_finite_cells (K : Set Ambient) (hK : IsCompact K) :
    ∃ S : Finset (Fin 3 → ℤ), K ⊆ ⋃ n ∈ S, translatedCell n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨N,hN⟩ := exists_nat_gt ((B+period)/period)
  let W : Set (Fin 3 → ℤ) := Set.univ.pi (fun _ => Icc (-(N : ℤ)) (N : ℤ))
  have hW : W.Finite := Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  refine ⟨hW.toFinset, ?_⟩
  intro k hk
  obtain ⟨n,q,hq,he⟩ := exists_cell_representative k
  have hn : n ∈ W := by
    intro i _
    have hkB : |k i| ≤ B := by
      exact (PiLp.norm_apply_le k i).trans (hB k hk)
    have hqB : |q i| ≤ period := by
      rw [abs_of_nonneg (hq i).1]
      exact (hq i).2.le
    have hni : (n i : ℝ)*period = k i-q i := by
      have hi := congrArg (fun v : Ambient => v i) he
      change k i = q i + (n i : ℝ)*period at hi
      linarith
    have hnb : |(n i : ℝ)| * period ≤ B+period := by
      rw [show |(n i : ℝ)| * period = |(n i : ℝ)*period| by
        rw [abs_mul, abs_of_pos period_pos], hni]
      exact (abs_sub _ _).trans (add_le_add hkB hqB)
    have hnf : |(n i : ℝ)| < (N : ℝ) := by
      exact ((le_div_iff₀ period_pos).mpr hnb).trans_lt hN
    have hl : -(N : ℝ) ≤ (n i : ℝ) := (abs_le.mp hnf.le).1
    have hu : (n i : ℝ) ≤ (N : ℝ) := (abs_le.mp hnf.le).2
    constructor
    · exact_mod_cast hl
    · exact_mod_cast hu
  apply mem_iUnion.mpr
  refine ⟨n, mem_iUnion.mpr ⟨hW.mem_toFinset.mpr hn, ?_⟩⟩
  exact ⟨q,hq,he.symm⟩

/-- A compact part of the real lift has bounded winding multiplicity over
the very same original quotient coarea. No global lifted mass is substituted
for the finite quotient energy. -/
theorem compact_quotient_domination {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (K : Set Ambient) (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ((liftedRegularCoarea d).restrict K).map quotientCoordinates ≤
        C • circleRegularCoarea d := by
  obtain ⟨S,hS⟩ := compact_finite_cells K hK
  refine ⟨(S.card : ℝ≥0∞), by simp, ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply quotientCoordinates_continuous.measurable hA,
    Measure.restrict_apply' hK.measurableSet]
  have hsub : quotientCoordinates ⁻¹' A ∩ K ⊆
      ⋃ n ∈ S, quotientCoordinates ⁻¹' A ∩ translatedCell n := by
    rintro k ⟨hkA,hkK⟩
    obtain ⟨n,hn'⟩ := mem_iUnion.mp (hS hkK)
    obtain ⟨hn,hkn⟩ := mem_iUnion.mp hn'
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, hkA, hkn⟩⟩
  calc
    _ ≤ (liftedRegularCoarea d) (⋃ n ∈ S, quotientCoordinates ⁻¹' A ∩ translatedCell n) :=
      measure_mono hsub
    _ ≤ ∑ n ∈ S, (liftedRegularCoarea d) (quotientCoordinates ⁻¹' A ∩ translatedCell n) :=
      measure_biUnion_finset_le S _
    _ = ∑ _n ∈ S, circleRegularCoarea d A := by
      apply Finset.sum_congr rfl
      intro n _
      have he := congrArg (fun μ : Measure CircleMomenta => μ A)
        (translatedCell_quotient_measure hd0 hdU n)
      simpa only [Measure.map_apply quotientCoordinates_continuous.measurable hA,
        Measure.restrict_apply' (translatedCell_measurable n)] using he
    _ = ((S.card : ℝ≥0∞) • circleRegularCoarea d) A := by
      simp [Measure.smul_apply, nsmul_eq_mul]

theorem compact_periodic_lintegral_le {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (K : Set Ambient) (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : CircleMomenta → ℝ≥0∞, Measurable F →
      (∫⁻ k in K, F (quotientCoordinates k) ∂liftedRegularCoarea d) ≤
        C * ∫⁻ q, F q ∂circleRegularCoarea d := by
  obtain ⟨C,hC,hdom⟩ := compact_quotient_domination hd0 hdU K hK
  refine ⟨C,hC,?_⟩
  intro F hF
  rw [← lintegral_map hF quotientCoordinates_continuous.measurable]
  exact (lintegral_mono' hdom le_rfl).trans_eq (lintegral_smul_measure C F)

end
end Resonance.PinnedCompactLocalization
