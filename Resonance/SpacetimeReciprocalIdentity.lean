import Resonance.SpacetimeActualMobility
import Resonance.SpacetimeContinuousDifference

/-! The original reciprocal collision relation at every full resonant
quartet, then on the one common spacetime measure. Both parameter fields
may vary: their inverse profiles remain the original five polynomials. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeReciprocalIdentity
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing SpacetimeContinuousFields
open WeightedJointMeasure ProfileBanachSmooth ContinuousMicroscopicFields
open ContinuousMicroscopicDifference ActualMicroscopicCurrent FiberContinuity
open ContinuousLogPath SpacetimeDifference Collision

def reciprocalFamily {R : ℝ} (c : ℝ) (F : Base→C(cube R,ℝ))
    (θ θc : Base→Parameter) (a : Base) : C(cube R,ℝ) :=
  yField c (F a) (profileMap R (θ a)) (profileMap R (θc a))

theorem dividedMicro_full_relation {R : ℝ} (c : ℝ) (f : C(cube R,ℝ))
    (hf : ∀k,f k≠0) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R)
    (q : FourMomenta) (hq : fullResonance R q) :
    halfDifference (dividedMicro c f θ θc) q=
      -(c/2)*delta (fun i=>(continuousExtension R f (q i))⁻¹) := by
  have he : delta (fun i=>(profile θc (q i))⁻¹)=0 := by
    simpa only [WeightedPhysicalForm.reciprocalProfile_eq_inv] using
      CollisionLinearization.reciprocalProfile_full_relation θc q hq.2.1 hq.2.2
  have hp (i:Fin 4) : continuousExtension R (dividedMicro c f θ θc) (q i)=
      c*((profile θc (q i))⁻¹-(continuousExtension R f (q i))⁻¹) := by
    rw [continuousExtension_eq R _ ⟨q i,hq.1 i⟩,dividedMicro_exact c f hf hθ hθc,
      ContinuousMap.smul_apply,ContinuousMap.sub_apply,smul_eq_mul,denominatorMap_apply,
      ring_inverse_apply f hf,continuousExtension_eq R f ⟨q i,hq.1 i⟩,
      profile_eq_inverse_denominator,inv_inv]
  simp only [halfDifference,hp,delta] at he ⊢
  linear_combination (c/2)*he

theorem joint_reciprocal_difference {R : ℝ} (T c : ℝ) (F : Base→C(cube R,ℝ))
    (θ θc : Base→Parameter)
    (hf : ∀ᵐa∂baseMeasure T,∀k,F a k≠0)
    (hθ : ∀ᵐa∂baseMeasure T,θ a∈positiveDomain R)
    (hθc : ∀ᵐa∂baseMeasure T,θc a∈positiveDomain R) :
    physicalRaw (θ:=θ) (field (reciprocalFamily c F θ θc))=ᵐ[SpacetimePairing.jointMeasure R T]
      (fun p=>-(c/2)*delta (fun i=>(field F (leg i p))⁻¹)) := by
  filter_upwards [joint_full_support R T,base_property_on_joint R T hf,
    base_property_on_joint R T hθ,base_property_on_joint R T hθc] with p hp hf ht htc
  rw [SpacetimeContinuousDifference.physicalRaw_field_point _ θ p hp.1]
  have hd:=dividedMicro_full_relation c (F p.1) hf ht htc p.2 hp
  have he (i:Fin 4) : continuousExtension R (F p.1) (p.2 i)=field F (leg i p) := by
    rw [continuousExtension_eq R _ ⟨p.2 i,hp.1 i⟩]
    exact (field_on_cube F p.1 ⟨p.2 i,hp.1 i⟩).symm
  simpa only [he] using hd

def productionField {R : ℝ} (F : Base→C(cube R,ℝ)) (p : Joint) : ℝ :=
  NonlinearEntropy.productionDensity (fun k=>field F (p.1,k)) p.2

theorem scaled_density_identity {R : ℝ} (T c : ℝ) (F : Base→C(cube R,ℝ))
    (θ θc : Base→Parameter)
    (hf : ∀ᵐa∂baseMeasure T,∀k,0<F a k)
    (hθ : ∀ᵐa∂baseMeasure T,θ a∈positiveDomain R)
    (hθc : ∀ᵐa∂baseMeasure T,θc a∈positiveDomain R) :
    (fun p=>SpacetimeActualMobility.actualWeight F p*
      ENNReal.ofReal ((physicalRaw (θ:=θ) (field (reciprocalFamily c F θ θc)) p)^2))
      =ᵐ[SpacetimePairing.jointMeasure R T]
      (fun p=>ENNReal.ofReal (c^2*productionField F p)) := by
  have hn : ∀ᵐa∂baseMeasure T,∀k,F a k≠0:=hf.mono (fun _ h k=>(h k).ne')
  filter_upwards [joint_reciprocal_difference T c F θ θc hn hθ hθc,
    joint_full_support R T,base_property_on_joint R T hf] with p hd hp hf
  have hprod : 0≤∏i:Fin 4,field F (leg i p) := by
    apply Finset.prod_nonneg
    intro i _
    exact (field_on_cube F p.1 ⟨p.2 i,hp.1 i⟩) ▸ (hf ⟨p.2 i,hp.1 i⟩).le
  rw [SpacetimeActualMobility.actualWeight,←ENNReal.ofReal_mul hprod,hd]
  apply congrArg ENNReal.ofReal
  simp only [productionField,NonlinearEntropy.productionDensity,mobility,leg]
  norm_num [Fin.prod_univ_succ,Fin.prod_univ_zero]
  rw [show (2:Fin 3).succ=(3:Fin 4) from rfl]
  ring

end
end Resonance.SpacetimeReciprocalIdentity
