import Resonance.PhysicalPairDensity

/-! The compact integral operator is the actual full physical collision
form in the coordinate f=nu_N*u, including genuine absolute integrability. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.LinftyPhysicalForm
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure WeightedJointMeasure CollisionFrequency FrequencyWeightedForm
open FrequencyGramDecomposition ActualPairNormalization ActualPairKernels
open PhysicalFrequencyCoordinates ReferenceFrequencySpace PhysicalPairDensity
open LinftyPhysicalDomain PhysicalWeightedCoercivity

theorem divided_pairing {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i j : Fin 4)
    {r : E×E→ℝ≥0∞} (hr : Measurable r) (hrf : ∀p,r p≠∞)
    (hp : (jointMeasure R θ).map (fun q=>(q i,q j))=
      ((cubeVolume R).prod (cubeVolume R)).withDensity r)
    (f : Lp ℝ ∞ (cubeVolume R)) (v : Space R) :
    Integrable (fun p : E×E=> (r p).toReal/
      (profile θ p.1*profile θ p.2*lossFrequency R (profile θ) p.2)*f p.2*v p.1)
      ((cubeVolume R).prod (cubeVolume R)) ∧
    inner ℝ (forward hR.le hθ v) (cross R θ i j (forward hR.le hθ (divide hR hθ f)))=
      ∫p,(r p).toReal/
        (profile θ p.1*profile θ p.2*lossFrequency R (profile θ) p.2)*f p.2*v p.1
        ∂(cubeVolume R).prod (cubeVolume R) := by
  letI := cubeVolume_finite R
  obtain ⟨hi,he⟩ := physical_density_pairing hR hθ i j hr hrf hp (divide hR hθ f) v
  have hc : (fun p : E×E=> (r p).toReal*((divide hR hθ f) p.2/profile θ p.2)*
      (v p.1/profile θ p.1))=ᵐ[(cubeVolume R).prod (cubeVolume R)]
      (fun p=> (r p).toReal/(profile θ p.1*profile θ p.2*
        lossFrequency R (profile θ) p.2)*f p.2*v p.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq
      (divide_ae_volume hR hθ f)] with p hp
    dsimp only [Function.comp_def] at hp
    rw [hp]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  exact ⟨hi.congr hc,he.trans (integral_congr_ae hc)⟩

theorem signed_pairing {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) (v : Space R) :
    Integrable (fun p : E×E=>AmbientLinftyCompact.kernel R θ p.1 p.2*f p.2*v p.1)
      ((cubeVolume R).prod (cubeVolume R)) ∧
    inner ℝ (forward hR.le hθ v) (cross R θ 0 1 (forward hR.le hθ (divide hR hθ f))) -
      2*inner ℝ (forward hR.le hθ v) (cross R θ 0 2 (forward hR.le hθ (divide hR hθ f)))=
      ∫p,AmbientLinftyCompact.kernel R θ p.1 p.2*f p.2*v p.1
        ∂(cubeVolume R).prod (cubeVolume R) := by
  obtain ⟨hi,he⟩ := divided_pairing hR hθ 0 1
    (IncomingPairDensity.density_measurable R (weight_measurable θ))
    (incoming_density_finite hθ) (incoming_pair_cube R θ) f v
  obtain ⟨hj,hf⟩ := divided_pairing hR hθ 0 2
    (CrossPairDensity.density_measurable R (weight_measurable θ))
    (cross_density_finite hR.le hθ) (cross_pair_cube hR.le θ) f v
  have halg : (fun p : E×E=>AmbientLinftyCompact.kernel R θ p.1 p.2*f p.2*v p.1)=
      (fun p=>(IncomingPairDensity.density R (weight θ) p).toReal/
        (profile θ p.1*profile θ p.2*lossFrequency R (profile θ) p.2)*f p.2*v p.1-
        2*((CrossPairDensity.density R (weight θ) p).toReal/
        (profile θ p.1*profile θ p.2*lossFrequency R (profile θ) p.2)*f p.2*v p.1)) := by
    funext p
    dsimp only [AmbientLinftyCompact.kernel]
    ring
  rw [halg]
  exact ⟨hi.sub (hj.const_mul 2),by rw [integral_sub hi (hj.const_mul 2),integral_const_mul,he,hf]⟩

theorem signed_pairing_iterated {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) (v : Space R) :
    inner ℝ (forward hR.le hθ v) (cross R θ 0 1 (forward hR.le hθ (divide hR hθ f))) -
      2*inner ℝ (forward hR.le hθ v) (cross R θ 0 2 (forward hR.le hθ (divide hR hθ f)))=
      ∫k,v k*(AmbientLinftyCompact.operator hR hθ f) k∂cubeVolume R := by
  letI := cubeVolume_finite R
  obtain ⟨hi,he⟩ := signed_pairing hR hθ f v
  rw [he,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [AmbientLinftyCompact.operator_ae hR hθ f] with k hk
  rw [hk,integral_mul_const,mul_comm]

theorem physical_diagonal {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u v : Space R) :
    Integrable (fun k=>lossFrequency R (profile θ) k*u k*v k) (cubeVolume R) ∧
    inner ℝ (forward hR.le hθ v) (forward hR.le hθ u)=
      ∫k,lossFrequency R (profile θ) k*u k*v k∂cubeVolume R := by
  let a : E→ℝ := forward hR.le hθ u
  let b : E→ℝ := forward hR.le hθ v
  have hi := L2.integrable_inner (𝕜 := ℝ) (forward hR.le hθ v) (forward hR.le hθ u)
  change Integrable (fun k=>a k*b k) (marginal R θ) at hi
  rw [marginal_cube_density hR.le θ] at hi
  have hif := (integrable_withDensity_iff_integrable_smul'
    (marginalDensity_measurable R θ)
    (ae_of_all _ (fun k=>(marginalDensity_finite hR.le hθ k).lt_top))).mp hi
  have ha : (fun k=>(marginalDensity R θ k).toReal •
      ((forward hR.le hθ u) k*(forward hR.le hθ v) k))=ᵐ[cubeVolume R]
      (fun k=>lossFrequency R (profile θ) k*u k*v k) := by
    filter_upwards [forward_ae_cube hR hθ u,forward_ae_cube hR hθ v,
      loss_positive_ae hR hθ,ae_restrict_mem (ResonantMeasure.measurable_cube R)] with k hu hv hl hk
    rw [hu,hv]
    change (CollisionMarginalDensity.fiberDensity R (weight θ) k).toReal *
      ((u k/profile θ k)*(v k/profile θ k))=_
    rw [CollisionMarginalDensity.weighted_density_eq_frequency hR.le hθ hk,
      ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hl.le)]
    field_simp [(profile_pos hθ hk).ne']
  refine ⟨hif.congr ha,?_⟩
  rw [L2.inner_def]
  change (∫k,a k*b k∂marginal R θ)=_
  rw [marginal_cube_density hR.le θ,
    integral_withDensity_eq_integral_toReal_smul (marginalDensity_measurable R θ)
      (ae_of_all _ (fun k=>(marginalDensity_finite hR.le hθ k).lt_top))]
  exact integral_congr_ae ha

theorem divided_diagonal {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) (v : Space R) :
    Integrable (fun k=>f k*v k) (cubeVolume R) ∧
    inner ℝ (forward hR.le hθ v) (forward hR.le hθ (divide hR hθ f))=
      ∫k,f k*v k∂cubeVolume R := by
  obtain ⟨hi,he⟩ := physical_diagonal hR hθ (divide hR hθ f) v
  have ha : (fun k=>lossFrequency R (profile θ) k*(divide hR hθ f) k*v k)
      =ᵐ[cubeVolume R] (fun k=>f k*v k) := by
    filter_upwards [frequency_divide_ae hR hθ f] with k hk
    rw [hk]
  exact ⟨hi.congr ha,he.trans (integral_congr_ae ha)⟩

theorem physicalForm_gram {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u v : Space R) :
    physicalForm hR hθ u v=
      inner ℝ (forward hR hθ v) (gram R θ (forward hR hθ u)) := by
  rw [gram_pairing]
  exact real_inner_comm _ _

theorem actual_form_identity {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) (v : Space R) :
    Integrable (fun k=>v k*(f k+(AmbientLinftyCompact.operator hR hθ f) k)) (cubeVolume R) ∧
    physicalForm hR.le hθ (divide hR hθ f) v=
      ∫k,v k*(f k+(AmbientLinftyCompact.operator hR hθ f) k)∂cubeVolume R := by
  have hi := (divided_diagonal hR hθ f v).1
  have hj := (divided_diagonal hR hθ (AmbientLinftyCompact.operator hR hθ f) v).1
  have ha : (fun k=>v k*(f k+(AmbientLinftyCompact.operator hR hθ f) k))=
      (fun k=>f k*v k+(AmbientLinftyCompact.operator hR hθ f) k*v k) := by
    funext k
    ring
  rw [ha]
  refine ⟨hi.add hj,?_⟩
  rw [physicalForm_gram,gram_eq_identity_add_cross]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.smul_apply,
    inner_sub_right,inner_add_right,inner_smul_right]
  rw [(divided_diagonal hR hθ f v).2,integral_add hi hj]
  have hp := signed_pairing_iterated hR hθ f v
  have hc : (∫k,v k*(AmbientLinftyCompact.operator hR hθ f) k∂cubeVolume R)=
      ∫k,(AmbientLinftyCompact.operator hR hθ f) k*v k∂cubeVolume R := by
    apply integral_congr_ae
    exact ae_of_all _ (fun _=>mul_comm _ _)
  rw [hc] at hp
  linarith

end
end Resonance.LinftyPhysicalForm
