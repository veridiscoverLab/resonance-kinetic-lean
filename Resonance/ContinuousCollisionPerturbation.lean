import Resonance.QuartetDerivativeBounds

/-! Actual same-quartet control of the full collision derivative near a
positive reference. The four leg squares are transported from the actual
common marginal to the fixed H_nu; no independent row measure is introduced.
Global smallness here is not a replacement for corner-localized smallness. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousCollisionPerturbation
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity ContinuousCollisionForm
open ContinuousCollisionMoments PhaseEnergy ContinuousWeightedEnergy
open FrequencyWeightedForm JointWeightComparison ReferenceMarginalTransport
open QuartetDerivativeBounds Collision CollisionLinearization WeakCollision
set_option maxHeartbeats 1500000

abbrev CubeFunction (R : ℝ) := C(MomentumDomain R,ℝ)

def toUnit {R : ℝ} (hR : 0<R) : ReferenceFrequencySpace.Space R→L[ℝ]H R unitParameter :=
  toMarginal hR.le (unitParameter_positive R)

theorem toUnit_ae {R : ℝ} (hR : 0<R) (u : CubeFunction R) :
    toUnit hR (toWeighted hR u)=ᵐ[marginal R unitParameter] continuousExtension R u := by
  exact (toMarginal_ae hR.le (unitParameter_positive R) _).trans
    ((WeightedJointMeasure.marginal_absolutelyContinuous_cube R unitParameter 0).ae_eq
      (toWeighted_ae hR u))

theorem leg_square_integrable {R : ℝ} (hR : 0<R) (u : CubeFunction R) (i : Fin 4) :
    Integrable (fun q:FourMomenta=>(continuousExtension R u (q i))^2) (pairingMeasure R) := by
  let v:=toUnit hR (toWeighted hR u)
  let w:=pullback R unitParameter i v
  have hw:= (pullback_ae R unitParameter i v).trans
    ((all_legs_preserve R unitParameter i).quasiMeasurePreserving.ae_eq (toUnit_ae hR u))
  have hi:= (Lp.memLp w).integrable_mul (Lp.memLp w)
  rw [←unit_joint R]
  exact hi.congr (by
    filter_upwards [hw] with q hq
    simp only [Function.comp_def] at hq
    simp only [Pi.mul_apply,w,hq,pow_two])

theorem leg_square_integral {R : ℝ} (hR : 0<R) (u : CubeFunction R) (i : Fin 4) :
    (∫q:FourMomenta,(continuousExtension R u (q i))^2∂pairingMeasure R)=
      ‖toUnit hR (toWeighted hR u)‖^2 := by
  let v:=toUnit hR (toWeighted hR u)
  let w:=pullback R unitParameter i v
  have hw:= (pullback_ae R unitParameter i v).trans
    ((all_legs_preserve R unitParameter i).quasiMeasurePreserving.ae_eq (toUnit_ae hR u))
  have he : (∫q,w q*w q∂WeightedJointMeasure.jointMeasure R unitParameter)=‖w‖^2 := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    rfl
  rw [←unit_joint R]
  calc
    _=(∫q,w q*w q∂WeightedJointMeasure.jointMeasure R unitParameter) := by
      apply integral_congr_ae
      filter_upwards [hw] with q hq
      simp only [Function.comp_def] at hq
      simp only [w,hq,pow_two]
    _=‖w‖^2 := he
    _=‖v‖^2 := by rw [(pullback R unitParameter i).norm_map]

theorem joint_square_sum_integrable {R : ℝ} (hR : 0<R) (u : CubeFunction R) :
    Integrable (fun q:FourMomenta=>∑i:Fin 4,(continuousExtension R u (q i))^2)
      (pairingMeasure R) := by
  exact integrable_finset_sum _ (fun i _=>leg_square_integrable hR u i)

theorem joint_square_sum_integral {R : ℝ} (hR : 0<R) (u : CubeFunction R) :
    (∫q:FourMomenta,∑i:Fin 4,(continuousExtension R u (q i))^2∂pairingMeasure R)=
      4*‖toUnit hR (toWeighted hR u)‖^2 := by
  rw [integral_finset_sum _ (fun i _=>leg_square_integrable hR u i)]
  simp_rw [leg_square_integral hR u]
  simp

theorem joint_square_sum_bound {R : ℝ} (hR : 0<R) (u : CubeFunction R) :
    (∫q:FourMomenta,∑i:Fin 4,(continuousExtension R u (q i))^2∂pairingMeasure R)≤
      (4*‖toUnit hR‖^2)*‖toWeighted hR u‖^2 := by
  rw [joint_square_sum_integral hR u]
  have hn:=(toUnit hR).le_opNorm (toWeighted hR u)
  have hs:=mul_self_le_mul_self (norm_nonneg _) hn
  nlinarith [sq_nonneg ‖toWeighted hR u‖]

def normalizedDensity (R : ℝ) (f N u : CubeFunction R) (q : FourMomenta) : ℝ :=
  (1/4:ℝ)*linearCoefficient (fun i=>continuousExtension R f (q i))
    (fun i=>continuousExtension R N (q i)*continuousExtension R u (q i))*
      delta (fun i=>continuousExtension R u (q i)/continuousExtension R N (q i))

theorem normalizedDensity_ae_linearDensity (R : ℝ) (f N u : CubeFunction R)
    (hN : ∀k,N k≠0) : normalizedDensity R f N u=ᵐ[pairingMeasure R]
      linearDensity (continuousExtension R f) (continuousExtension R (N*u))
        (continuousExtension R (u*inverseCube N hN)) := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  have hd : (fun i:Fin 4=>continuousExtension R (N*u) (q i))=
      (fun i=>continuousExtension R N (q i)*continuousExtension R u (q i)) := by
    funext i
    rw [continuousExtension_eq R (N*u) ⟨q i,hq.1 i⟩,
      continuousExtension_eq R N ⟨q i,hq.1 i⟩,continuousExtension_eq R u ⟨q i,hq.1 i⟩]
    rfl
  have ht : (fun i:Fin 4=>continuousExtension R (u*inverseCube N hN) (q i))=
      (fun i=>continuousExtension R u (q i)/continuousExtension R N (q i)) := by
    funext i
    rw [continuousExtension_eq R (u*inverseCube N hN) ⟨q i,hq.1 i⟩,
      continuousExtension_eq R u ⟨q i,hq.1 i⟩,continuousExtension_eq R N ⟨q i,hq.1 i⟩]
    rfl
  simp only [normalizedDensity,linearDensity,hd,ht]

theorem normalizedDensity_integrable {R : ℝ} (hR : 0≤R) (f N u : CubeFunction R)
    (hN : ∀k,N k≠0) : Integrable (normalizedDensity R f N u) (pairingMeasure R) :=
  (linearDensity_integrable hR (extension_memLp R f) (extension_memLp R (N*u))
    (extension_memLp R (u*inverseCube N hN))).congr
      (normalizedDensity_ae_linearDensity R f N u hN).symm

def perturbationDensity (R : ℝ) (f N u : CubeFunction R) (q : FourMomenta) : ℝ :=
  (1/4:ℝ)*(linearCoefficient (fun i=>continuousExtension R f (q i))
    (fun i=>continuousExtension R N (q i)*continuousExtension R u (q i))-
      linearCoefficient (fun i=>continuousExtension R N (q i))
        (fun i=>continuousExtension R N (q i)*continuousExtension R u (q i)))*
          delta (fun i=>continuousExtension R u (q i)/continuousExtension R N (q i))

theorem perturbationDensity_sub (R : ℝ) (f N u : CubeFunction R) :
    perturbationDensity R f N u=normalizedDensity R f N u-normalizedDensity R N N u := by
  funext q
  simp only [perturbationDensity,normalizedDensity,Pi.sub_apply]
  ring

theorem perturbationDensity_integrable {R : ℝ} (hR : 0≤R) (f N u : CubeFunction R)
    (hN : ∀k,N k≠0) : Integrable (perturbationDensity R f N u) (pairingMeasure R) := by
  rw [perturbationDensity_sub]
  exact (normalizedDensity_integrable hR f N u hN).sub
    (normalizedDensity_integrable hR N N u hN)

theorem actual_perturbation_integral {R : ℝ} (hR : 0≤R) (f N u : CubeFunction R)
    (hN : ∀k,N k≠0) :
    cubeIntegral R ((u*inverseCube N hN)*
      (fderiv ℝ (collisionMap R hR) f (N*u)-fderiv ℝ (collisionMap R hR) N (N*u)))=
        ∫q,perturbationDensity R f N u q∂pairingMeasure R := by
  rw [mul_sub,map_sub,normalized_fderiv_full_pairing,normalized_fderiv_full_pairing,
    perturbationDensity_sub]
  exact (integral_sub (normalizedDensity_integrable hR f N u hN)
    (normalizedDensity_integrable hR N N u hN)).symm

/-- The perturbation is estimated in the actual fixed H_nu norm, with all
four inputs and all test legs on the same original sharp resonance measure. -/
theorem actual_full_derivative_perturbation {R : ℝ} (hR : 0<R)
    (f N u : CubeFunction R) {m M δ : ℝ} (hm : 0 < m) (hM : 0≤M) (hδ : 0≤δ)
    (hf : ∀k,|f k|≤M) (hN : ∀k,m≤N k ∧ |N k|≤M) (hd : ∀k,|f k-N k|≤δ) :
    |cubeIntegral R ((u*inverseCube N (fun k=>(lt_of_lt_of_le hm (hN k).1).ne'))*
      (fderiv ℝ (collisionMap R hR.le) f (N*u)-fderiv ℝ (collisionMap R hR.le) N (N*u)))|≤
        ((24*M^2*‖toUnit hR‖^2/m)*δ)*‖toWeighted hR u‖^2 := by
  let hNz : ∀k,N k≠0:=fun k=>(lt_of_lt_of_le hm (hN k).1).ne'
  have hi:=perturbationDensity_integrable hR.le f N u hNz
  have hb : ∀ᵐ q∂pairingMeasure R, |perturbationDensity R f N u q|≤
      (6*M^2*δ/m)*(∑i:Fin 4,(continuousExtension R u (q i))^2) := by
    filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
    apply normalized_energy_perturbation_bound _ _ _ hm hM hδ
    · intro i
      rw [continuousExtension_eq R f ⟨q i,hq.1 i⟩]
      exact hf _
    · intro i
      rw [continuousExtension_eq R N ⟨q i,hq.1 i⟩]
      exact hN _
    · intro i
      rw [continuousExtension_eq R f ⟨q i,hq.1 i⟩,
        continuousExtension_eq R N ⟨q i,hq.1 i⟩]
      exact hd _
  rw [actual_perturbation_integral]
  calc
    _≤∫q,|perturbationDensity R f N u q|∂pairingMeasure R :=
      abs_integral_le_integral_abs
    _≤∫q,(6*M^2*δ/m)*(∑i:Fin 4,(continuousExtension R u (q i))^2)∂pairingMeasure R :=
      integral_mono_ae hi.abs ((joint_square_sum_integrable hR u).const_mul _) hb
    _=(6*M^2*δ/m)*(∫q,∑i:Fin 4,(continuousExtension R u (q i))^2∂pairingMeasure R) :=
      integral_const_mul _ _
    _≤(6*M^2*δ/m)*((4*‖toUnit hR‖^2)*‖toWeighted hR u‖^2) :=
      mul_le_mul_of_nonneg_left (joint_square_sum_bound hR u) (by positivity)
    _=_ := by ring

/-- Actual nonlinear derivative dissipation on each compact positive RJ
family, under global smallness of f-N. This statement retains the original
five physical orthogonality integrals and does not assert a corner-localized
version with non-small corner amplitude. -/
theorem actual_near_rj_micro_dissipation {R : ℝ} (hR : 0<R)
    {K : Set Thermodynamics.Parameter} (hK : IsCompact K)
    (hpos : K⊆Thermodynamics.positiveDomain R) :
    ∃κ γ:ℝ,0<κ ∧ 0<γ ∧ ∀θ,(hθ:θ∈K)→∀f u:CubeFunction R,
      (∀k,|f k-rjCube (hpos hθ) k|≤κ)→
      (∀i,cubeIntegral R (u*basisCube (hpos hθ) i)=0)→
      cubeIntegral R ((u*inverseCube (rjCube (hpos hθ))
        (fun k=>(rjCube_pos (hpos hθ) k).ne'))*
          fderiv ℝ (collisionMap R hR.le) f (rjCube (hpos hθ)*u))≤
            -γ*‖toWeighted hR u‖^2 := by
  obtain ⟨m,M,hm,hM,hb⟩:=compact_profile_bounds hR.le hK hpos
  obtain ⟨γ,hγ,hco⟩:=actual_rj_micro_dissipation hR hK hpos
  let C:=24*(M+1)^2*‖toUnit hR‖^2/m
  have hC:0≤C:=by dsimp [C]; positivity
  let κ:=min 1 (γ/(2*(C+1)))
  have hk:0<κ:=lt_min (by norm_num) (div_pos hγ (by positivity))
  have hk1:κ≤1:=min_le_left _ _
  have hkγ:C*κ≤γ/2 := by
    have h:= (le_div_iff₀ (show 0<2*(C+1) by positivity)).mp (min_le_right 1 (γ/(2*(C+1))))
    change κ*(2*(C+1))≤γ at h
    nlinarith
  refine ⟨κ,γ/2,hk,by positivity,?_⟩
  intro θ hθ f u hf hu
  let N:=rjCube (hpos hθ)
  have hNb : ∀k,m≤N k ∧ |N k|≤M+1 := by
    intro k
    have hp:=hb θ hθ k k.property
    refine ⟨hp.1,?_⟩
    rw [abs_of_pos (rjCube_pos (hpos hθ) k)]
    exact hp.2.trans (by linarith)
  have hfb : ∀k,|f k|≤M+1 := by
    intro k
    have ht:=abs_add_le (f k-N k) (N k)
    rw [sub_add_cancel] at ht
    have hfk:=hf k
    have hn:= (hb θ hθ k k.property).2
    rw [abs_of_pos (rjCube_pos (hpos hθ) k)] at ht
    change |f k-N k|≤κ at hfk
    change N k≤M at hn
    linarith
  have hp:=actual_full_derivative_perturbation hR f N u hm (by positivity) hk.le hfb hNb hf
  have hd:=hco θ hθ u hu
  rw [mul_sub,map_sub] at hp
  change |cubeIntegral R ((u*inverseCube N _)*fderiv ℝ (collisionMap R hR.le) f (N*u))-
      cubeIntegral R ((u*inverseCube N _)*fderiv ℝ (collisionMap R hR.le) N (N*u))|≤
        (C*κ)*‖toWeighted hR u‖^2 at hp
  have he:=le_abs_self (cubeIntegral R ((u*inverseCube N (fun k=>(rjCube_pos (hpos hθ) k).ne'))*
      fderiv ℝ (collisionMap R hR.le) f (N*u))-
    cubeIntegral R ((u*inverseCube N (fun k=>(rjCube_pos (hpos hθ) k).ne'))*
      fderiv ℝ (collisionMap R hR.le) N (N*u)))
  have hbγ:=mul_le_mul_of_nonneg_right hkγ (sq_nonneg ‖toWeighted hR u‖)
  dsimp [N] at hp he
  linarith

end
end Resonance.ContinuousCollisionPerturbation

#check Resonance.ContinuousCollisionPerturbation.toUnit_ae
#check Resonance.ContinuousCollisionPerturbation.leg_square_integrable
#check Resonance.ContinuousCollisionPerturbation.leg_square_integral
#check Resonance.ContinuousCollisionPerturbation.joint_square_sum_integrable
#check Resonance.ContinuousCollisionPerturbation.joint_square_sum_integral
#check Resonance.ContinuousCollisionPerturbation.joint_square_sum_bound
#check Resonance.ContinuousCollisionPerturbation.normalizedDensity_ae_linearDensity
#check Resonance.ContinuousCollisionPerturbation.normalizedDensity_integrable
#check Resonance.ContinuousCollisionPerturbation.perturbationDensity_sub
#check Resonance.ContinuousCollisionPerturbation.perturbationDensity_integrable
#check Resonance.ContinuousCollisionPerturbation.actual_perturbation_integral
#check Resonance.ContinuousCollisionPerturbation.actual_full_derivative_perturbation
#check Resonance.ContinuousCollisionPerturbation.actual_near_rj_micro_dissipation
#print axioms Resonance.ContinuousCollisionPerturbation.toUnit_ae
#print axioms Resonance.ContinuousCollisionPerturbation.leg_square_integrable
#print axioms Resonance.ContinuousCollisionPerturbation.leg_square_integral
#print axioms Resonance.ContinuousCollisionPerturbation.joint_square_sum_integrable
#print axioms Resonance.ContinuousCollisionPerturbation.joint_square_sum_integral
#print axioms Resonance.ContinuousCollisionPerturbation.joint_square_sum_bound
#print axioms Resonance.ContinuousCollisionPerturbation.normalizedDensity_ae_linearDensity
#print axioms Resonance.ContinuousCollisionPerturbation.normalizedDensity_integrable
#print axioms Resonance.ContinuousCollisionPerturbation.perturbationDensity_sub
#print axioms Resonance.ContinuousCollisionPerturbation.perturbationDensity_integrable
#print axioms Resonance.ContinuousCollisionPerturbation.actual_perturbation_integral
#print axioms Resonance.ContinuousCollisionPerturbation.actual_full_derivative_perturbation
#print axioms Resonance.ContinuousCollisionPerturbation.actual_near_rj_micro_dissipation
