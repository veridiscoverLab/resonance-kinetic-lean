import Resonance.PinnedScaledDifference
import Resonance.ClosedOperatorRepresentation
import Resonance.PinnedGap

/-! The nonnegative selfadjoint realization of the original maximal
periodic full-coarea form, including its exact γ/4 normalization. -/
open Real Set MeasureTheory Filter LinearPMap
open scoped Topology ENNReal ComplexConjugate
namespace Resonance.PinnedOperator
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedMaximalDifference Resonance.PinnedSmoothDomain
open Resonance.PinnedClosedForm Resonance.PinnedScaledDifference
open Resonance.ClosedOperatorRepresentation
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

def associatedOperator {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) : Source →ₗ.[ℂ] Source :=
  square (scaledDifference hd0 hdU a γ)

theorem associatedOperator_selfAdjoint {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0<γ) :
    IsSelfAdjoint (associatedOperator hd0 hdU a γ) :=
  square_selfAdjoint _ (scaledDifference_dense_domain hd0 hdU ha γ)
    (scaledDifference_isClosed hd0 hdU a hγ)

theorem associatedOperator_graph_iff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0≤γ) (x z : Source) :
    (x,z)∈(associatedOperator hd0 hdU a γ).graph ↔
      ∃hx:x∈(maximalDifference hd0 hdU a).domain,
        ∀y:FormDomain hd0 hdU a,inner ℂ z (y:Source)=form hd0 hdU a γ ⟨x,hx⟩ y := by
  rw [associatedOperator,square_graph_iff _ (scaledDifference_dense_domain hd0 hdU ha γ)]
  simp only [scaledDifference_domain,scaled_inner_eq_form hd0 hdU a hγ]

theorem associatedOperator_eq_scaled_square {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0<γ) :
    associatedOperator hd0 hdU a γ=(γ/4:ℂ) • square (maximalDifference hd0 hdU a) := by
  let T := maximalDifference hd0 hdU a
  let b : ℂ := γ/4
  have hb : b≠0 := by dsimp [b]; exact div_ne_zero (Complex.ofReal_ne_zero.mpr hγ.ne') (by norm_num)
  have hbconj : (starRingEnd ℂ) b=b := by change star b=b; simp [b]
  have hTi := maximalDifference_dense_domain hd0 hdU ha
  apply LinearPMap.eq_of_eq_graph
  apply SetLike.coe_injective
  apply Set.ext
  intro p
  change (p.1,p.2)∈(associatedOperator hd0 hdU a γ).graph ↔
    p∈((γ/4:ℂ) • square (maximalDifference hd0 hdU a)).graph
  rw [associatedOperator_graph_iff hd0 hdU ha hγ.le]
  change (∃hx:p.1∈T.domain,∀y:T.domain,inner ℂ p.2 (y:Source)=b*inner ℂ (T ⟨p.1,hx⟩) (T y)) ↔
    p∈(b • square T).graph
  constructor
  · rintro ⟨hx,hv⟩
    have hs : (p.1,b⁻¹ • p.2)∈(square T).graph := by
      apply (square_graph_iff T hTi _ _).mpr
      refine ⟨hx,fun y=>?_⟩
      rw [inner_smul_left,map_inv₀,hbconj,hv,←mul_assoc,inv_mul_cancel₀ hb,one_mul]
    obtain ⟨u,hu,hval⟩ := (LinearPMap.mem_graph_iff _).mp hs
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨u,hu,?_⟩
    rw [LinearPMap.smul_apply,hval,smul_inv_smul₀ hb]
  · intro hs
    obtain ⟨u,hu,hval⟩ := (LinearPMap.mem_graph_iff _).mp hs
    have hx : p.1∈T.domain := hu ▸ u.property.choose
    refine ⟨hx,fun y=>?_⟩
    rw [←hval,LinearPMap.smul_apply,inner_smul_left,hbconj,square_pairing T hTi]
    have he : squareDomainInclusion T u=⟨p.1,hx⟩ := Subtype.ext hu
    rw [he]

/-- The domain is the literal adjoint-square domain of the unscaled
maximal difference. There is no smooth-core assumption. -/
theorem associatedOperator_domain_iff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0<γ) (x : Source) :
    x∈(associatedOperator hd0 hdU a γ).domain ↔
      ∃hx:x∈(maximalDifference hd0 hdU a).domain,
        maximalDifference hd0 hdU a ⟨x,hx⟩∈(maximalDifference hd0 hdU a)†.domain := by
  rw [associatedOperator_eq_scaled_square hd0 hdU ha hγ,LinearPMap.smul_domain]
  exact square_domain_iff _ x

theorem associatedOperator_zero_graph_iff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0<γ) (x : Source) :
    (x,0)∈(associatedOperator hd0 hdU a γ).graph ↔
      (x,0)∈(maximalDifference hd0 hdU a).graph := by
  rw [associatedOperator_graph_iff hd0 hdU ha hγ.le]
  constructor
  · rintro ⟨hx,hv⟩
    have hh := hv ⟨x,hx⟩
    rw [inner_zero_left,form,inner_self_eq_norm_sq_to_K] at hh
    have hb : (γ/4:ℂ)≠0 := div_ne_zero (Complex.ofReal_ne_zero.mpr hγ.ne') (by norm_num)
    have ht : maximalDifference hd0 hdU a ⟨x,hx⟩=0 := by
      have hsq := (mul_eq_zero.mp hh.symm).resolve_left hb
      exact norm_eq_zero.mp (Complex.ofReal_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨x,hx⟩,rfl,ht⟩
  · intro hx
    obtain ⟨u,hu,hzero⟩ := (LinearPMap.mem_graph_iff _).mp hx
    change (u:Source)=x at hu
    have hxD : x∈(maximalDifference hd0 hdU a).domain := hu ▸ u.property
    refine ⟨hxD,fun y=>?_⟩
    have he : (⟨x,hxD⟩:FormDomain hd0 hdU a)=u := Subtype.ext hu.symm
    simp [he,form,hzero]

theorem associatedOperator_kernel_classification {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (hapos : ∀ k, 0<a k)
    {γ : ℝ} (hγ : 0<γ) (x : Source) :
    (x,0)∈(associatedOperator hd0 hdU a γ).graph ↔
      ExistsUnique (fun AB : ℂ × ℂ => (x:PinnedPeriodicity.Circle→ℂ) =ᵐ[circleHaar]
        (fun k=>AB.1+AB.2*(PinnedEndToEnd.circleDispersion d k:ℂ))) := by
  rw [associatedOperator_zero_graph_iff hd0 hdU ha hγ,maximalDifference_graph]
  exact maximalGraph_kernel_classification hd0 hdU a ha hapos x

theorem finite_energy_eq_ofReal_integral {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (u : FormDomain hd0 hdU a) :
    PinnedGap.energy d a (u:Source)=
      ENNReal.ofReal (∫ k,‖difference (u:Source) k‖^2 ∂weightedCoarea d a) := by
  rw [ofReal_integral_eq_lintegral_ofReal (full_square_integrable hd0 hdU a u)
    (Eventually.of_forall (fun _=>sq_nonneg _))]
  unfold PinnedGap.energy
  apply lintegral_congr
  intro k
  rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]

theorem form_spectral_gap {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (hapos : ∀ k, 0<a k) :
    ∃ lam : ℝ, 0<lam ∧ ∀ (γ : ℝ), 0≤γ → ∀ u : FormDomain hd0 hdU a,
      (γ/4)*lam*‖(u:Source)-(PinnedGap.nullSpace hd0 hdU a).starProjection u‖^2
        ≤(form hd0 hdU a γ u u).re := by
  obtain ⟨lam,hlam,hgap⟩ := PinnedGap.full_coarea_spectral_gap hd0 hdU a ha hapos
  refine ⟨lam,hlam,fun γ hγ u=>?_⟩
  have h := hgap (u:Source)
  rw [finite_energy_eq_ofReal_integral hd0 hdU a u] at h
  have hn : ENNReal.ofReal lam*‖(u:Source)-(PinnedGap.nullSpace hd0 hdU a).starProjection u‖ₑ^2=
      ENNReal.ofReal (lam*‖(u:Source)-(PinnedGap.nullSpace hd0 hdU a).starProjection u‖^2) := by
    rw [ENNReal.ofReal_mul hlam.le,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  rw [hn] at h
  have hi0 : 0≤∫ k,‖difference (u:Source) k‖^2 ∂weightedCoarea d a :=
    integral_nonneg (fun _=>sq_nonneg _)
  have hr := (ENNReal.ofReal_le_ofReal_iff hi0).mp h
  rw [form_diagonal]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr (div_nonneg hγ (by norm_num))

theorem associatedOperator_dense_domain {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0<γ) :
    Dense ((associatedOperator hd0 hdU a γ).domain : Set Source) :=
  (associatedOperator_selfAdjoint hd0 hdU ha hγ).dense_domain

theorem associatedOperator_nonnegative {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (γ : ℝ)
    (u : (associatedOperator hd0 hdU a γ).domain) :
    0≤(inner ℂ (associatedOperator hd0 hdU a γ u) (u:Source)).re :=
  square_nonnegative _ (scaledDifference_dense_domain hd0 hdU ha γ) u

/-- Uniqueness is stated for the full original maximal form domain.
It is not uniqueness among arbitrary operators agreeing only on C². -/
theorem associatedOperator_unique_form_realization {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0≤γ)
    (L : Source →ₗ.[ℂ] Source)
    (hL : ∀ x z : Source,(x,z)∈L.graph ↔
      ∃hx:x∈(maximalDifference hd0 hdU a).domain,
        ∀y:FormDomain hd0 hdU a,inner ℂ z (y:Source)=form hd0 hdU a γ ⟨x,hx⟩ y) :
    L=associatedOperator hd0 hdU a γ := by
  apply LinearPMap.eq_of_eq_graph
  apply SetLike.coe_injective
  apply Set.ext
  rintro ⟨x,z⟩
  exact (hL x z).trans (associatedOperator_graph_iff hd0 hdU ha hγ x z).symm

theorem associatedOperator_kernel_eq_nullSpace {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0<γ) :
    (associatedOperator hd0 hdU a γ).graph.comap
      ((LinearMap.id : Source→ₗ[ℂ]Source).prod (0:Source→ₗ[ℂ]Source))=
        PinnedGap.nullSpace hd0 hdU a := by
  apply Submodule.ext
  intro x
  change (x,0)∈(associatedOperator hd0 hdU a γ).graph ↔
    (x,0)∈maximalGraph d a
  rw [associatedOperator_zero_graph_iff hd0 hdU ha hγ,maximalDifference_graph]
  rfl

/-- The manuscript uses the first-linear convention, opposite to Lean's
inner-product argument order. This is an explicit dictionary, not an
identification of two different sesquilinear conventions. -/
def paperInner (u v : Source) : ℂ := inner ℂ v u
def paperForm {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (a : FourCircle→ℝ) (γ : ℝ)
    (u v : FormDomain hd0 hdU a) : ℂ := form hd0 hdU a γ v u

theorem form_conj_symm {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) (u v : FormDomain hd0 hdU a) :
    conj (form hd0 hdU a γ u v)=form hd0 hdU a γ v u := by
  unfold form
  rw [map_mul,inner_conj_symm]
  have hc : conj (γ/4:ℂ)=(γ/4:ℂ) := by change star (γ/4:ℂ)=(γ/4:ℂ); simp
  rw [hc]

theorem paperForm_integral {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) (u v : FormDomain hd0 hdU a) :
    paperForm hd0 hdU a γ u v=(γ/4:ℂ)*
      ∫ k,difference (u:Source) k*conj (difference (v:Source) k) ∂weightedCoarea d a := by
  rw [paperForm,form_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun _=>mul_comm _ _)

theorem associatedOperator_paper_graph_iff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0≤γ) (x z : Source) :
    (x,z)∈(associatedOperator hd0 hdU a γ).graph ↔
      ∃hx:x∈(maximalDifference hd0 hdU a).domain,
        ∀y:FormDomain hd0 hdU a,paperInner z (y:Source)=paperForm hd0 hdU a γ ⟨x,hx⟩ y := by
  rw [associatedOperator_graph_iff hd0 hdU ha hγ]
  constructor
  · rintro ⟨hx,hv⟩
    refine ⟨hx,fun y=>?_⟩
    have he := congrArg conj (hv y)
    rw [inner_conj_symm,form_conj_symm] at he
    exact he
  · rintro ⟨hx,hv⟩
    refine ⟨hx,fun y=>?_⟩
    have he := congrArg conj (hv y)
    change conj (inner ℂ (y:Source) z)=conj (form hd0 hdU a γ y ⟨x,hx⟩) at he
    rw [inner_conj_symm,form_conj_symm] at he
    exact he

theorem scaledFormGraph_complete {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) {γ : ℝ} (hγ : 0<γ) :
    CompleteSpace (ClosedOperatorRepresentation.graphHilbert
      (scaledDifference hd0 hdU a γ)) :=
  (ClosedOperatorRepresentation.graphHilbert_isClosed _
    (scaledDifference_isClosed hd0 hdU a hγ)).isComplete.completeSpace_coe

theorem scaledFormGraph_norm_square {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) {γ : ℝ} (hγ : 0≤γ)
    (u : ClosedOperatorRepresentation.graphHilbert (scaledDifference hd0 hdU a γ)) :
    ‖u‖^2=‖(WithLp.ofLp (u:WithLp 2 (Source × Target d a))).1‖^2+
      (γ/4)*(∫ k,‖difference ((WithLp.ofLp (u:WithLp 2 (Source × Target d a))).1) k‖^2
        ∂weightedCoarea d a) := by
  let f : Source := (WithLp.ofLp (u:WithLp 2 (Source × Target d a))).1
  let g : Target d a := (WithLp.ofLp (u:WithLp 2 (Source × Target d a))).2
  have hu : (f,g)∈(scaledDifference hd0 hdU a γ).graph := u.property
  obtain ⟨v,hvf,hvg⟩ := (LinearPMap.mem_graph_iff _).mp hu
  change (v:Source)=f at hvf
  change scaledDifference hd0 hdU a γ v=g at hvg
  have hc : ‖factor γ‖^2=γ/4 := by
    simpa only [factor,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      using Real.sq_sqrt (div_nonneg hγ (show (0:ℝ)≤4 by norm_num))
  change ‖(u:WithLp 2 (Source × Target d a))‖^2=‖f‖^2+_
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖f‖^2+‖g‖^2=‖f‖^2+_
  rw [←hvg,scaledDifference_apply,norm_smul,mul_pow,hc,operator_norm_square_integral]
  congr 2
  exact congrArg (fun t:Source=>∫ k,‖difference t k‖^2 ∂weightedCoarea d a) hvf

/-- The original maximal closed-form theorem. Smooth-domain inclusion,
density, the adjoint-square domain and selfadjointness are conclusions,
not hypotheses. The full integral and gap normalizations are given by
`form_integral`, `form_diagonal` and `form_spectral_gap`. -/
theorem pinned_closed_theorem {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) {γ : ℝ} (hγ : 0<γ) :
    (maximalDifference hd0 hdU a).IsClosed ∧
    Dense ((maximalDifference hd0 hdU a).domain : Set Source) ∧
    (∀φ:C(PinnedPeriodicity.Circle,ℂ),ContDiff ℝ 2 (periodicLift φ)→
      ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ φ∈(maximalDifference hd0 hdU a).domain) ∧
    IsSelfAdjoint (associatedOperator hd0 hdU a γ) ∧
    (associatedOperator hd0 hdU a γ=(γ/4:ℂ) • square (maximalDifference hd0 hdU a)) ∧
    (∀x:Source,x∈(associatedOperator hd0 hdU a γ).domain ↔
      ∃hx:x∈(maximalDifference hd0 hdU a).domain,
        maximalDifference hd0 hdU a ⟨x,hx⟩∈(maximalDifference hd0 hdU a)†.domain) :=
  ⟨maximalDifference_isClosed hd0 hdU a,maximalDifference_dense_domain hd0 hdU ha,
    continuous_C2_mem_domain hd0 hdU ha,associatedOperator_selfAdjoint hd0 hdU ha hγ,
    associatedOperator_eq_scaled_square hd0 hdU ha hγ,
    associatedOperator_domain_iff hd0 hdU ha hγ⟩

end
end Resonance.PinnedOperator
