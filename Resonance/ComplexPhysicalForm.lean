import Resonance.ComplexLpDecomposition

/-! The original complex four-leg form on the fixed reference space,
with the paper's first-variable-linear convention and uniform microcoercivity. -/
open MeasureTheory Set
namespace Resonance.ComplexPhysicalForm
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity ComplexLpDecomposition

abbrev ComplexSpace (R : ℝ) := Lp ℂ 2 (referenceMeasure R)

def rawDifference (f : E→ℂ) (q : FourMomenta) : ℂ :=
  (1/2 : ℂ)*(f (q 0)+f (q 1)-f (q 2)-f (q 3))

def difference {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ComplexSpace R→L[ℝ]Lp ℂ 2 (jointMeasure R θ) := lift (physicalDifference hR hθ)

theorem parts_on_legs {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : ComplexSpace R) : ∀ᵐq∂jointMeasure R θ,∀i : Fin 4,
      realPart (referenceMeasure R) u (q i)=(u (q i)).re ∧
      imagPart (referenceMeasure R) u (q i)=(u (q i)).im := by
  have hac : FrequencyWeightedForm.marginal R θ≪referenceMeasure R :=
    Measure.absolutelyContinuous_of_le_smul
      (Classical.choose_spec (ReferenceMarginalTransport.actual_domination hR hθ)).2
  have hr := hac.ae_eq (realPart_ae u)
  have hi := hac.ae_eq (imagPart_ae u)
  apply ae_all_iff.mpr
  intro i
  exact ((FrequencyWeightedForm.all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq hr).and
    ((FrequencyWeightedForm.all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq hi)

theorem difference_ae {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : ComplexSpace R) : (difference hR hθ u : FourMomenta→ℂ)=ᵐ[jointMeasure R θ]
      rawDifference (fun k=>u k/(profile θ k : ℂ)) := by
  filter_upwards [lift_ae (physicalDifference hR hθ) u,
    physicalDifference_ae hR hθ (realPart (referenceMeasure R) u),
    physicalDifference_ae hR hθ (imagPart (referenceMeasure R) u),parts_on_legs hR hθ u]
    with q hq hr hi hp
  change lift (physicalDifference hR hθ) u q=_
  rw [hq,hr,hi]
  unfold rawDifference CollisionForm.rawDifference
  apply Complex.ext <;> simp [Complex.div_ofReal_re,Complex.div_ofReal_im,
    (hp 0).1,(hp 1).1,(hp 2).1,(hp 3).1,(hp 0).2,(hp 1).2,(hp 2).2,(hp 3).2]

def form {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u v : ComplexSpace R) : ℂ := inner ℂ (difference hR hθ v) (difference hR hθ u)

theorem form_integrable {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u v : ComplexSpace R) : Integrable (fun q=>
      rawDifference (fun k=>u k/(profile θ k : ℂ)) q*
      star (rawDifference (fun k=>v k/(profile θ k : ℂ)) q)) (jointMeasure R θ) := by
  apply (L2.integrable_inner (𝕜:=ℂ) (difference hR hθ v) (difference hR hθ u)).congr
  filter_upwards [difference_ae hR hθ u,difference_ae hR hθ v] with q hu hv
  change difference hR hθ u q*star (difference hR hθ v q)=_
  rw [hu,hv]

theorem form_integral {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u v : ComplexSpace R) : form hR hθ u v=∫q,
      rawDifference (fun k=>u k/(profile θ k : ℂ)) q*
      star (rawDifference (fun k=>v k/(profile θ k : ℂ)) q)∂jointMeasure R θ := by
  rw [form,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [difference_ae hR hθ u,difference_ae hR hθ v] with q hu hv
  change difference hR hθ u q*star (difference hR hθ v q)=_
  rw [hu,hv]

theorem form_self {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : ComplexSpace R) : form hR hθ u u=(‖difference hR hθ u‖^2 : ℝ) := by
  unfold form
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem form_real_parts {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : ComplexSpace R) : (form hR hθ u u).re=
      physicalForm hR hθ (realPart (referenceMeasure R) u) (realPart (referenceMeasure R) u)+
      physicalForm hR hθ (imagPart (referenceMeasure R) u) (imagPart (referenceMeasure R) u) := by
  rw [form_self,Complex.ofReal_re,physical_form_square,physical_form_square]
  exact lift_norm_square (physicalDifference hR hθ) u

def projection {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ComplexSpace R→L[ℝ]ComplexSpace R := lift (PhysicalMomentProjection.projection hR hθ)

theorem complex_microcoercivity {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃c C : ℝ,0 < c ∧ 0≤C ∧ ∀θ,(hθ : θ∈K) → ∀u : ComplexSpace R,
      projection hR (hpos hθ) u=0 →
      c*‖u‖^2≤(form hR.le (hpos hθ) u u).re ∧
      (form hR.le (hpos hθ) u u).re≤C*‖u‖^2 := by
  obtain ⟨c,C,hc,hC,hgap⟩ := PhysicalMicroCoercivity.actual_microcoercivity hR hK hpos
  refine ⟨c,C,hc,hC,?_⟩
  intro θ hθ u hu
  have hr : PhysicalMomentProjection.projection hR (hpos hθ) (realPart (referenceMeasure R) u)=0 := by
    rw [←realPart_lift,show lift (PhysicalMomentProjection.projection hR (hpos hθ)) u=0 from hu,
      map_zero]
  have hi : PhysicalMomentProjection.projection hR (hpos hθ) (imagPart (referenceMeasure R) u)=0 := by
    rw [←imagPart_lift,show lift (PhysicalMomentProjection.projection hR (hpos hθ)) u=0 from hu,
      map_zero]
  obtain ⟨hr1,hr2⟩ := hgap θ hθ (realPart (referenceMeasure R) u) hr
  obtain ⟨hi1,hi2⟩ := hgap θ hθ (imagPart (referenceMeasure R) u) hi
  rw [form_real_parts,norm_square_parts u]
  constructor <;> nlinarith

end
end Resonance.ComplexPhysicalForm
