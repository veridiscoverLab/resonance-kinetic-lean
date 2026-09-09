import Resonance.ProductL2Slices
import Resonance.SpacetimeRJIntegration
import Resonance.PhysicalFrequencyCoordinates

/-! Exact disintegration of the common difference norm into the original
parameter-dependent Hilbert differences. This supplies the actual norm
dictionary for integrating the uniform five-Gram recovery inequality. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeDifferenceSlices
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing SpacetimeReference
open SpacetimeDifference WeightedJointMeasure ProductL2Slices

theorem lp_square_lintegral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (u : Lp ℝ 2 μ) : ENNReal.ofReal (‖u‖^2)=∫⁻a,ENNReal.ofReal ((u a)^2)∂μ := by
  have he : ‖u‖^2=∫a,(u a)^2∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    exact ae_of_all _ (fun a=>by change u a*u a=(u a)^2; ring)
  rw [he]
  apply ofReal_integral_eq_lintegral_ofReal
  · simpa only [Real.norm_eq_abs,sq_abs] using (Lp.memLp u).integrable_norm_pow (by norm_num)
  · exact ae_of_all _ (fun a=>sq_nonneg _)

theorem physicalRaw_measurable {R : ℝ} (hR : 0≤R) (T : ℝ) {θ : Base→Parameter}
    (hm : Measurable θ) {u : Source→ℝ} (hu : Measurable u) :
    Measurable (physicalRaw (θ:=θ) u) := by
  have hd:Measurable (fun z:Source=>u z/profile (θ z.1) z.2):=
    hu.div (SpacetimeRJMeasure.joint_profile_measurable.comp
      ((hm.comp measurable_fst).prodMk measurable_snd))
  have hh (i:Fin 4):Measurable (fun p:Joint=>u (leg i p)/profile (θ p.1) (p.2 i)):=
    hd.comp (SpacetimePairing.leg_quasiMeasurePreserving hR T i).measurable
  exact (((hh 0).add (hh 1) |>.sub (hh 2)).sub (hh 3)).const_mul (1/2:ℝ)

theorem fiber_ae {R : ℝ} (hR : 0<R) (T : ℝ) (u : Space R T)
    (a : Base) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (hu : (slice u a:E→ℝ)=ᵐ[ReferenceFrequencySpace.referenceMeasure R](fun k=>u (a,k))) :
    PhysicalFrequencyCoordinates.physicalDifference hR.le hθ (slice u a)=ᵐ[jointMeasure R θ]
      (fun q=>CollisionForm.rawDifference (fun k=>u (a,k)/profile θ k) q) := by
  have hp (i:Fin 4) : QuasiMeasurePreserving (fun q:FourMomenta=>q i)
      (jointMeasure R θ) (ReferenceFrequencySpace.referenceMeasure R) :=
    ⟨(leg_quasiMeasurePreserving_cube R θ i).measurable,
      (marginal_absolutelyContinuous_cube R θ i).trans
        (ReferenceFrequencySpace.reference_volume_equivalent hR).1⟩
  filter_upwards [PhysicalFrequencyCoordinates.physicalDifference_ae hR.le hθ (slice u a),
    (hp 0).ae_eq hu,(hp 1).ae_eq hu,(hp 2).ae_eq hu,(hp 3).ae_eq hu]
    with q hq h0 h1 h2 h3
  rw [hq]
  simp only [Function.comp_def] at h0 h1 h2 h3
  simp only [CollisionForm.rawDifference,h0,h1,h2,h3]

def sliceEnergy {R : ℝ} (hR : 0≤R) (T : ℝ) (θ : Base→Parameter)
    (u : Space R T) (a : Base) : ℝ := by
  classical
  exact if hθ:θ a∈positiveDomain R then
    ‖PhysicalFrequencyCoordinates.physicalDifference hR hθ (slice u a)‖^2 else 0

theorem full_norm_disintegration {R : ℝ} (hR : 0<R) (T : ℝ)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R)
    {θ : Base→Parameter} (hm : Measurable θ) (hθ : ∀ᵐa∂baseMeasure T,θ a∈K)
    (u : Space R T) :
    ENNReal.ofReal (‖physicalDifference hR T hK hpos hm hθ u‖^2)=
      ∫⁻a,ENNReal.ofReal (sliceEnergy hR.le T θ u a)∂baseMeasure T := by
  letI:=reference_finite hR.le
  have hs:=slice_ae u
  have hraw:=physicalRaw_measurable hR.le T hm (Lp.stronglyMeasurable u).measurable
  calc
    _=∫⁻p,ENNReal.ofReal ((physicalRaw (θ:=θ) u p)^2)∂SpacetimeRJMeasure.measure R T θ := by
      rw [lp_square_lintegral]
      exact lintegral_congr_ae ((physicalDifference_ae hR T hK hpos hm hθ u).fun_comp
        (fun x:ℝ=>ENNReal.ofReal (x^2)))
    _=∫⁻a,∫⁻q,ENNReal.ofReal ((physicalRaw (θ:=θ) u (a,q))^2)
        ∂jointMeasure R (θ a)∂baseMeasure T :=
      SpacetimeRJIntegration.full_lintegral hR.le T hm _ ((hraw.pow_const 2).ennreal_ofReal)
    _=_ := by
      apply lintegral_congr_ae
      filter_upwards [hs,hθ] with a hs hθ
      have ha:=hpos hθ
      simp only [sliceEnergy,dif_pos ha]
      rw [lp_square_lintegral]
      apply lintegral_congr_ae
      filter_upwards [fiber_ae hR T u a ha hs] with q hq
      rw [hq]
      rfl

end
end Resonance.SpacetimeDifferenceSlices
