import Resonance.ContinuousCollisionPerturbation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The original complete nonlinear collision difference, obtained by
integrating the actual Banach derivative along the same two states. The
reference and physical microcondition remain fixed along this segment. -/
open Set MeasureTheory
namespace Resonance.NonlinearCollisionDissipation
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity ContinuousCollisionForm
open ContinuousCollisionMoments PhaseEnergy ContinuousWeightedEnergy
open ContinuousCollisionPerturbation CollisionMultilinear
set_option maxHeartbeats 1500000

abbrev CubeFunction (R : ℝ) := C(MomentumDomain R,ℝ)

def segment (f F : CubeFunction R) (t : ℝ) : CubeFunction R := F+t • (f-F)

theorem segment_zero (f F : CubeFunction R) : segment f F 0=F := by simp [segment]
theorem segment_one (f F : CubeFunction R) : segment f F 1=f := by simp [segment]

theorem segment_near (f F N : CubeFunction R) {κ t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hf : ∀k,|f k-N k|≤κ) (hF : ∀k,|F k-N k|≤κ) :
    ∀k,|segment f F t k-N k|≤κ := by
  intro k
  change |F k+t*(f k-F k)-N k|≤κ
  calc
    _=|(1-t)*(F k-N k)+t*(f k-N k)| := by congr 1; ring
    _≤|(1-t)*(F k-N k)|+|t*(f k-N k)| := abs_add_le _ _
    _=(1-t)*|F k-N k|+t*|f k-N k| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1]
    _≤(1-t)*κ+t*κ := add_le_add
      (mul_le_mul_of_nonneg_left (hF k) (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hf k) ht.1)
    _=κ := by ring

theorem collision_segment_pairing_hasDerivAt {R : ℝ} (hR : 0≤R)
    (f F g : CubeFunction R) (t : ℝ) :
    HasDerivAt (fun s:ℝ=>cubeIntegral R (g*collisionMap R hR (segment f F s)))
      (cubeIntegral R (g*fderiv ℝ (collisionMap R hR) (segment f F t) (f-F))) t := by
  let L : CubeFunction R→L[ℝ]ℝ :=
    (cubeIntegral R).comp (ContinuousLinearMap.mul ℝ (CubeFunction R) g)
  have hp : HasDerivAt (segment f F) (f-F) t := by
    simpa only [segment,id_eq,one_smul] using ((hasDerivAt_id t).smul_const (f-F)).const_add F
  have hc := (collisionMap_hasFDerivAt hR (segment f F t)).comp_hasDerivAt t hp
  rw [←(collisionMap_hasFDerivAt hR (segment f F t)).fderiv] at hc
  exact L.hasFDerivAt.comp_hasDerivAt t hc

/-- A two-state estimate for the actual collision map. Neither state is
replaced by a linearized model, and the derivative at every intervening state
is the full original cubic derivative. -/
theorem actual_nonlinear_micro_dissipation {R : ℝ} (hR : 0<R)
    {K : Set Thermodynamics.Parameter} (hK : IsCompact K)
    (hpos : K⊆Thermodynamics.positiveDomain R) :
    ∃κ γ:ℝ,0<κ ∧ 0<γ ∧ ∀θ,(hθ:θ∈K)→∀f F u:CubeFunction R,
      (∀k,|f k-rjCube (hpos hθ) k|≤κ)→
      (∀k,|F k-rjCube (hpos hθ) k|≤κ)→
      f-F=rjCube (hpos hθ)*u→
      (∀i,cubeIntegral R (u*basisCube (hpos hθ) i)=0)→
      cubeIntegral R ((u*inverseCube (rjCube (hpos hθ))
        (fun k=>(rjCube_pos (hpos hθ) k).ne'))*
          (collisionMap R hR.le f-collisionMap R hR.le F))≤
            -γ*‖toWeighted hR u‖^2 := by
  obtain ⟨κ,γ,hκ,hγ,hder⟩:=actual_near_rj_micro_dissipation hR hK hpos
  refine ⟨κ,γ,hκ,hγ,?_⟩
  intro θ hθ f F u hf hF hu horth
  let N:=rjCube (hpos hθ)
  let g:=u*inverseCube N (fun k=>(rjCube_pos (hpos hθ) k).ne')
  let φ:=fun s:ℝ=>cubeIntegral R (g*collisionMap R hR.le (segment f F s))
  have hd (s:ℝ) : HasDerivAt φ
      (cubeIntegral R (g*fderiv ℝ (collisionMap R hR.le) (segment f F s) (N*u))) s := by
    have h:=collision_segment_pairing_hasDerivAt hR.le f F g s
    rw [hu] at h
    exact h
  have hdiff : Differentiable ℝ φ:=fun s=>(hd s).differentiableAt
  have hle : ∀s∈interior (Icc (0:ℝ) 1),deriv φ s≤-γ*‖toWeighted hR u‖^2 := by
    intro s hs
    rw [(hd s).deriv]
    exact hder θ hθ (segment f F s) u (segment_near f F N (interior_subset hs) hf hF) horth
  have hb := (convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn hle
    0 (by simp) 1 (by simp) (by norm_num)
  simpa only [φ,segment_one,segment_zero,sub_zero,mul_one,←map_sub,←mul_sub] using hb

def invariantCube (R : ℝ) (i : Fin 5) : CubeFunction R :=
  ⟨fun k=>CoareaNormalization.euclideanFive i k,
    (CoareaNormalization.euclideanFive_continuous i).comp continuous_subtype_val⟩

def normalizedDifference (f F N : CubeFunction R) (hN : ∀k,N k≠0) : CubeFunction R :=
  (f-F)*inverseCube N hN

theorem normalizedDifference_identity (f F N : CubeFunction R) (hN : ∀k,N k≠0) :
    N*normalizedDifference f F N hN=f-F := by
  ext k
  change N k*((f k-F k)*(N k)⁻¹)=f k-F k
  field_simp [hN k]

theorem normalizedDifference_micro {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f F : CubeFunction R)
    (hm : ∀i,cubeIntegral R (f*invariantCube R i)=cubeIntegral R (F*invariantCube R i)) :
    ∀i,cubeIntegral R (normalizedDifference f F (rjCube hθ)
      (fun k=>(rjCube_pos hθ k).ne')*basisCube hθ i)=0 := by
  intro i
  have he : normalizedDifference f F (rjCube hθ) (fun k=>(rjCube_pos hθ k).ne')*
      basisCube hθ i=(f-F)*invariantCube R i := by
    ext k
    change ((f k-F k)*(WeightedJointMeasure.profile θ k)⁻¹)*
      (WeightedJointMeasure.profile θ k*CoareaNormalization.euclideanFive i k)=_
    change ((f k-F k)*(WeightedJointMeasure.profile θ k)⁻¹)*
      (WeightedJointMeasure.profile θ k*CoareaNormalization.euclideanFive i k)=
        (f k-F k)*CoareaNormalization.euclideanFive i k
    field_simp [(WeightedJointMeasure.profile_pos hθ k.property).ne']
  rw [he,sub_mul,map_sub,hm,sub_self]

/-- Same actual five moments, expressed as the original unweighted cube
integrals, suffice for nonlinear dissipation of the actual normalized
difference. No separate Hilbert-space micro hypothesis is imposed. -/
theorem actual_matched_nonlinear_dissipation {R : ℝ} (hR : 0<R)
    {K : Set Thermodynamics.Parameter} (hK : IsCompact K)
    (hpos : K⊆Thermodynamics.positiveDomain R) :
    ∃κ γ:ℝ,0<κ ∧ 0<γ ∧ ∀θ,(hθ:θ∈K)→∀f F:CubeFunction R,
      (∀k,|f k-rjCube (hpos hθ) k|≤κ)→
      (∀k,|F k-rjCube (hpos hθ) k|≤κ)→
      (∀i,cubeIntegral R (f*invariantCube R i)=cubeIntegral R (F*invariantCube R i))→
      let u:=normalizedDifference f F (rjCube (hpos hθ))
        (fun k=>(rjCube_pos (hpos hθ) k).ne')
      cubeIntegral R ((u*inverseCube (rjCube (hpos hθ))
        (fun k=>(rjCube_pos (hpos hθ) k).ne'))*
          (collisionMap R hR.le f-collisionMap R hR.le F))≤
            -γ*‖toWeighted hR u‖^2 := by
  obtain ⟨κ,γ,hκ,hγ,hb⟩:=actual_nonlinear_micro_dissipation hR hK hpos
  refine ⟨κ,γ,hκ,hγ,?_⟩
  intro θ hθ f F hf hF hm
  exact hb θ hθ f F _ hf hF (normalizedDifference_identity f F _ _).symm
    (normalizedDifference_micro (hpos hθ) f F hm)

end
end Resonance.NonlinearCollisionDissipation

#check Resonance.NonlinearCollisionDissipation.segment_zero
#check Resonance.NonlinearCollisionDissipation.segment_one
#check Resonance.NonlinearCollisionDissipation.segment_near
#check Resonance.NonlinearCollisionDissipation.collision_segment_pairing_hasDerivAt
#check Resonance.NonlinearCollisionDissipation.actual_nonlinear_micro_dissipation
#check Resonance.NonlinearCollisionDissipation.normalizedDifference_identity
#check Resonance.NonlinearCollisionDissipation.normalizedDifference_micro
#check Resonance.NonlinearCollisionDissipation.actual_matched_nonlinear_dissipation
#print axioms Resonance.NonlinearCollisionDissipation.segment_zero
#print axioms Resonance.NonlinearCollisionDissipation.segment_one
#print axioms Resonance.NonlinearCollisionDissipation.segment_near
#print axioms Resonance.NonlinearCollisionDissipation.collision_segment_pairing_hasDerivAt
#print axioms Resonance.NonlinearCollisionDissipation.actual_nonlinear_micro_dissipation
#print axioms Resonance.NonlinearCollisionDissipation.normalizedDifference_identity
#print axioms Resonance.NonlinearCollisionDissipation.normalizedDifference_micro
#print axioms Resonance.NonlinearCollisionDissipation.actual_matched_nonlinear_dissipation
