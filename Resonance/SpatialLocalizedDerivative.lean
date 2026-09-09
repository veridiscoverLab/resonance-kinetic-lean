import Resonance.FullLocalizedDerivativeSplit
import Resonance.MoserReferenceEnergy

/-! Space and momentum remain in one history. The full localized
cross error is integrated for the same N(X,k), f(X,k), and energy field;
no time-path theorem is transplanted to spatial transport. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.SpatialLocalizedDerivative
noncomputable section
open ResonantMeasure FreeTransport SpatialIntegrationByParts SpatialMomentumSections
open JointEnergyReader MoserReferenceEnergy LocalizedDerivativeCoefficients
open ActualLocalizedOffDiagonal FullLocalizedDerivativeSplit
open ContinuousCollisionPerturbation ContinuousWeightedEnergy JointWeightComparison
set_option maxHeartbeats 2200000

def offHistory {R : ℝ} (f N u : Section R) (z : History) : ℝ:=
  offDiagonalPart (fun i=>leg f i z) (fun i=>leg N i z) (fun i=>leg u i z)

theorem offHistory_measurable {R : ℝ} (f N u : Section R) : Measurable (offHistory f N u) := by
  unfold offHistory offDiagonalPart
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij:i=j
  · simp only [hij,if_true]
    exact measurable_const
  · simp only [hij,if_false]
    exact ((relativeCoefficient_measurable _ _ (fun l=>leg_evaluate_measurable f l)
      (fun l=>leg_evaluate_measurable N l) i j).mul (leg_evaluate_measurable u i)).mul
      (leg_evaluate_measurable u j)

theorem offDiagonalPart_bound (f N u : Collision.Quartet) {m M U : ℝ}
    (hm : 0 < m) (hM : 0≤M) (hU : 0≤U) (hf : ∀i,|f i|≤M)
    (hN : ∀i,m≤N i ∧ |N i|≤M) (hu : ∀i,|u i|≤U) :
    |offDiagonalPart f N u|≤192*M^3/m*U^2 := by
  have hd : ∀i,|f i-N i|≤2*M:=by
    intro i
    have ha:=abs_sub (f i) (N i)
    linarith [hf i,(hN i).2]
  have hc (i j:Fin 4) : |relativeCoefficient f N i j|≤12*M^3/m := by
    have h:=relativeCoefficient_bound f N hm hM (by positivity : 0≤2*M) hf hN hd i j
    exact h.trans_eq (by ring)
  unfold offDiagonalPart
  calc
    _≤∑i:Fin 4,|∑j:Fin 4,if i=j then 0 else relativeCoefficient f N i j*u i*u j|:=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑i:Fin 4,∑j:Fin 4,|if i=j then 0 else relativeCoefficient f N i j*u i*u j|:=
      Finset.sum_le_sum (fun i _=>Finset.abs_sum_le_sum_abs _ _)
    _≤∑_i:Fin 4,∑_j:Fin 4,(12*M^3/m)*U^2:=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij:i=j
      · simp only [hij,if_true,abs_zero]
        positivity
      · simp only [hij,if_false,abs_mul]
        have hh:=mul_le_mul (mul_le_mul (hc i j) (hu i) (abs_nonneg _) (by positivity))
          (hu j) (abs_nonneg _) (by positivity)
        simpa only [pow_two,mul_assoc] using hh
    _=_:=by simp; ring

theorem offHistory_integrable {R : ℝ} (hR : 0<R) (f N u : Section R)
    {m M : ℝ} (hm : 0 < m) (hM : 0≤M)
    (hf : ∀X k,|f k X|≤M) (hN : ∀X k,m≤N k X ∧ |N k X|≤M) :
    Integrable (offHistory f N u) (volume.prod (pairingMeasure R)) := by
  letI:=pairingMeasure_finite hR.le
  apply Integrable.of_bound (offHistory_measurable f N u).aestronglyMeasurable (192*M^3/m*‖u‖^2)
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ:=(volume:Measure SpatialTorus))
    (ν:=pairingMeasure R)).ae (ae_iff.mpr (pairing_supported_on_fullResonance R))] with z hz
  rw [Real.norm_eq_abs]
  apply offDiagonalPart_bound _ _ _ hm hM (norm_nonneg u)
  · intro i
    rw [show leg f i z=f ⟨z.2 i,hz.1 i⟩ z.1 from evaluate_on f z.1 ⟨z.2 i,hz.1 i⟩]
    exact hf _ _
  · intro i
    rw [show leg N i z=N ⟨z.2 i,hz.1 i⟩ z.1 from evaluate_on N z.1 ⟨z.2 i,hz.1 i⟩]
    exact hN _ _
  · intro i
    exact evaluate_bound u z.1 (z.2 i)

theorem slice_offHistory_identity {R : ℝ} (f N u : Section R) (X : SpatialTorus) :
    (fun q=>offHistory f N u (X,q))=ᵐ[pairingMeasure R]
      offDensity R (spatialSlice f X) (spatialSlice N X) (spatialSlice u X) := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  have hleg (h:Section R) : (fun i:Fin 4=>leg h i (X,q))=
      (fun i=>FiberContinuity.continuousExtension R (spatialSlice h X) (q i)) := by
    funext i
    rw [show leg h i (X,q)=h ⟨q i,hq.1 i⟩ X from evaluate_on h X ⟨q i,hq.1 i⟩,
      FiberContinuity.continuousExtension_eq R (spatialSlice h X) ⟨q i,hq.1 i⟩]
    rfl
  change offDiagonalPart _ _ _=_
  rw [hleg f,hleg N,hleg u]
  rfl

/-- The energy norm and the nonlinear coefficient use the same space
variable. This is the actual spatial/quartet product integral. -/
theorem actual_spatial_offdiagonal_bound {R : ℝ} (hR : 0<R) (f N u : Section R)
    {m M κ η : ℝ} (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ)
    (hf : ∀X k,|f k X|≤M) (hN : ∀X k,m≤N k X ∧ |N k X|≤M)
    (hbulk : ∀X (k:MomentumDomain R),η<CornerFrequencyBounds.cornerDepth R k → |f k X-N k X|≤κ) :
    |∫z,offHistory f N u z∂volume.prod (pairingMeasure R)|≤
      (16*energyCost R m M κ η*‖toUnit hR‖^2)*
        (∫X,‖toWeighted hR (spatialSlice u X)‖^2) := by
  letI:=pairingMeasure_finite hR.le
  have hi:=offHistory_integrable hR f N u hm hM hf hN
  have he:=(actual_reference_section_identity hR u).1
  let C:ℝ:=16*energyCost R m M κ η*‖toUnit hR‖^2
  rw [integral_prod _ hi,←integral_const_mul]
  have hd : ∀ᵐX∂(volume:Measure SpatialTorus),
      ‖∫q,offHistory f N u (X,q)∂pairingMeasure R‖≤C*‖toWeighted hR (spatialSlice u X)‖^2 := by
    apply ae_of_all
    intro X
    rw [integral_congr_ae (slice_offHistory_identity f N u X),Real.norm_eq_abs]
    exact (actual_full_offdiagonal_estimate hR (spatialSlice f X) (spatialSlice N X)
      (spatialSlice u X) hm hM hκ (hf X) (hN X) (hbulk X)).2
  simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le (he.const_mul C) hd

/-- A single coefficient field controls the entire finite energy family,
so later coframe jets retain their common spatial and quartet history. -/
theorem actual_joint_energy_family_bound {R : ℝ} (hR : 0<R) {A : Type*} [Fintype A]
    (f N : Section R) (u : A→Section R) {m M κ η : ℝ}
    (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ)
    (hf : ∀X k,|f k X|≤M) (hN : ∀X k,m≤N k X ∧ |N k X|≤M)
    (hbulk : ∀X (k:MomentumDomain R),η<CornerFrequencyBounds.cornerDepth R k → |f k X-N k X|≤κ) :
    |∑a,∫z,offHistory f N (u a) z∂volume.prod (pairingMeasure R)|≤
      (16*energyCost R m M κ η*‖toUnit hR‖^2)*
        (∑a,∫X,‖toWeighted hR (spatialSlice (u a) X)‖^2) := by
  calc
    _≤∑a,|∫z,offHistory f N (u a) z∂volume.prod (pairingMeasure R)|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑a,(16*energyCost R m M κ η*‖toUnit hR‖^2)*
        (∫X,‖toWeighted hR (spatialSlice (u a) X)‖^2):=
      Finset.sum_le_sum (fun a _=>actual_spatial_offdiagonal_bound hR f N (u a) hm hM hκ hf hN hbulk)
    _=_:=(Finset.mul_sum _ _ _).symm

end
end Resonance.SpatialLocalizedDerivative
