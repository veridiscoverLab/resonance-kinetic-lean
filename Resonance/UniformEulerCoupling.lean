import Resonance.GramCoefficientContinuity
import Resonance.ResonantMeasure

/-! A uniform coupling variance on every compact positive RJ parameter set,
with actual Euclidean spatial frequency. -/
open Set
namespace Resonance.UniformEulerCoupling
noncomputable section
set_option maxHeartbeats 800000
open Thermodynamics GramCouplingVariance GramCoefficientContinuity ActualEulerCoupling
open ResonantMeasure

theorem variance_smul (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) (a : ℝ) :
    variance R θ (a • ell)=a^2*variance R θ ell := by
  have hb : betaDirection (a • ell)=a • betaDirection ell := by
    funext i
    fin_cases i <;> simp [betaDirection]
  simp only [variance,hb,quadratic,cross,Matrix.mulVec_smul,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

theorem variance_zero (R : ℝ) (θ : Parameter) : variance R θ (0 : Fin 3→ℝ)=0 := by
  have he := variance_smul R θ (0 : Fin 3→ℝ) 0
  simpa only [zero_smul,zero_pow (by norm_num : (2 : ℕ)≠0),zero_mul] using he

theorem actual_unit_coupling_bounds {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃a A : ℝ,0<a ∧ 0<A ∧ ∀θ∈K,∀w∈Metric.sphere (0 : E) 1,
      a≤variance R θ (fun i=>w i) ∧ variance R θ (fun i=>w i)≤A := by
  let V := fun p : Parameter×E=>variance R p.1 (fun i=>p.2 i)
  have hc : ContinuousOn V (K×ˢMetric.sphere (0 : E) 1) := by
    have hcoords : Continuous (fun p : Parameter×E=>(p.1,fun i=>p.2 i)) := by
      exact continuous_fst.prodMk (continuous_pi fun i=>
        ((PiLp.proj 2 (fun _ : Fin 3=>ℝ) i : E→L[ℝ]ℝ).continuous.comp continuous_snd))
    exact ContinuousOn.comp
      (g := fun p : Parameter×(Fin 3→ℝ)=>variance R p.1 p.2)
      (f := fun p : Parameter×E=>(p.1,fun i=>p.2 i))
      (s := K×ˢMetric.sphere (0 : E) 1) (t := (positiveDomain R)×ˢuniv)
      (original_variance_continuousOn R hR) hcoords.continuousOn
      (fun _ hp=>⟨hpos hp.1,mem_univ _⟩)
  have hp : ∀p∈K×ˢMetric.sphere (0 : E) 1,0<V p := by
    intro p hp
    apply actual_coupling_variance_positive R hR p.1 (hpos hp.1)
    intro he
    have hz : p.2=0 := by ext i; exact congrFun he i
    simpa [hz] using hp.2
  by_cases hn : (K×ˢMetric.sphere (0 : E) 1).Nonempty
  · obtain ⟨p,hp0,hmin⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn hn hc
    obtain ⟨q,hq0,hmax⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMaxOn hn hc
    refine ⟨V p,V q,hp p hp0,hp q hq0,?_⟩
    intro θ hθ w hw
    change V p≤V (θ,w) ∧ V (θ,w)≤V q
    exact ⟨@hmin (θ,w) ⟨hθ,hw⟩,@hmax (θ,w) ⟨hθ,hw⟩⟩
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro θ hθ w hw
    exact (hn ⟨(θ,w),hθ,hw⟩).elim

theorem actual_all_frequency_coupling_bounds {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃a A : ℝ,0<a ∧ 0<A ∧ ∀θ∈K,∀ell : E,
      a*‖ell‖^2≤variance R θ (fun i=>ell i) ∧
      variance R θ (fun i=>ell i)≤A*‖ell‖^2 := by
  obtain ⟨a,A,ha,hA,hb⟩ := actual_unit_coupling_bounds hR hK hpos
  refine ⟨a,A,ha,hA,?_⟩
  intro θ hθ ell
  by_cases hz : ell=0
  · subst ell
    simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero]
    change (0≤variance R θ (0 : Fin 3→ℝ)) ∧ variance R θ (0 : Fin 3→ℝ)≤0
    rw [variance_zero]
    exact ⟨le_refl _,le_refl _⟩
  have hn : 0<‖ell‖ := norm_pos_iff.mpr hz
  let w : E := ‖ell‖⁻¹ • ell
  have hw : w∈Metric.sphere (0 : E) 1 := by
    simp [w,norm_smul,hn.ne']
  have he : (fun i=>ell i)=‖ell‖ • (fun i=>w i) := by
    funext i
    simp [w,hn.ne']
  have hbound := hb θ hθ w hw
  rw [he,variance_smul]
  constructor
  · nlinarith [sq_nonneg ‖ell‖]
  · nlinarith [sq_nonneg ‖ell‖]

end
end Resonance.UniformEulerCoupling
