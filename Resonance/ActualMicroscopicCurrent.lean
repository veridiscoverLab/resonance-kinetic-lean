import Resonance.ContinuousMicroscopicDifference

/-! Original continuous collision output and full signed current. The
same reciprocal coordinate gives both the weak identity and the entropy
square, with all four parents and the physical factors 1/2 and 1/4. -/
open Set MeasureTheory
namespace Resonance.ActualMicroscopicCurrent
noncomputable section
open ResonantMeasure Thermodynamics ProfileBanachSmooth FiberContinuity
open ContinuousMicroscopicDifference ContinuousCollisionMoments ContinuousCollisionForm
open ContinuousCollisionEntropy NonlinearEntropy WeakCollision Collision

def halfDifference {R : ℝ} (g : C(cube R,ℝ)) (q : FourMomenta) : ℝ :=
  (1/2:ℝ)*delta (fun i=>continuousExtension R g (q i))

def fullMobility {R : ℝ} (f : C(cube R,ℝ)) (q : FourMomenta) : ℝ :=
  mobility (fun i=>continuousExtension R f (q i))

theorem weak_density_identity {R : ℝ} (c : ℝ) (f g : C(cube R,ℝ))
    (hf : ∀ k,0<f k) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    ∀ᵐ q ∂pairingMeasure R,
      c*density (continuousExtension R f) (continuousExtension R (denominatorMap R θ*g)) q=
      -(fullMobility f q*halfDifference (dividedMicro c f θ θc) q*
        halfDifference (denominatorMap R θ*g) q) := by
  filter_upwards [dividedMicro_difference_ae c f (fun k=>(hf k).ne') hθ hθc,
    all_legs_pos_ae (positive_extension f hf)] with q hd hp
  simp only [density,full_weak_reciprocal_identity _ _ (fun i=>(hp i).ne'),
    halfDifference,fullMobility,hd]
  ring

theorem entropy_density_identity {R : ℝ} (c : ℝ) (f : C(cube R,ℝ))
    (hf : ∀ k,f k≠0) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    ∀ᵐ q ∂pairingMeasure R,c^2*productionDensity (continuousExtension R f) q=
      fullMobility f q*halfDifference (dividedMicro c f θ θc) q^2 := by
  filter_upwards [dividedMicro_difference_ae c f hf hθ hθc] with q hd
  simp only [productionDensity,fullMobility,halfDifference,hd]
  ring

theorem physical_signed_current_identity {R : ℝ} (c : ℝ) (f : C(cube R,ℝ))
    (hf : ∀ k,f k≠0) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    ∀ᵐ q ∂pairingMeasure R,
      (c/2)*Real.sqrt (fullMobility f q)*delta (fun i=>(continuousExtension R f (q i))⁻¹)=
      -Real.sqrt (fullMobility f q)*halfDifference (dividedMicro c f θ θc) q := by
  filter_upwards [dividedMicro_difference_ae c f hf hθ hθc] with q hd
  simp only [halfDifference,hd]
  ring

theorem microscopic_pairing_integrable {R : ℝ} (hR : 0≤R) (c : ℝ)
    (f g : C(cube R,ℝ)) (hf : ∀ k,0<f k) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    Integrable (fun q=>fullMobility f q*halfDifference (dividedMicro c f θ θc) q*
      halfDifference (denominatorMap R θ*g) q) (pairingMeasure R) := by
  have hi := (density_integrable hR (extension_memLp R f)
    (extension_memLp R (denominatorMap R θ*g))).const_mul (-c)
  apply hi.congr
  filter_upwards [weak_density_identity c f g hf hθ hθc] with q hq
  linarith

theorem microscopic_square_integrable {R : ℝ} (hR : 0≤R) (c : ℝ)
    (f : C(cube R,ℝ)) (hf : ∀ k,0<f k) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    Integrable (fun q=>fullMobility f q*halfDifference (dividedMicro c f θ θc) q^2)
      (pairingMeasure R) :=
  ((cubeProduction_integrable_quartet hR f hf).const_mul (c^2)).congr
    (entropy_density_identity c f (fun k=>(hf k).ne') hθ hθc)

theorem original_scaled_weak_collision {R : ℝ} (hR : 0≤R) (c : ℝ)
    (f g : C(cube R,ℝ)) (hf : ∀ k,0<f k) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    c*cubeIntegral R ((denominatorMap R θ*g)*collisionMap R hR f)=
      -(∫q,fullMobility f q*halfDifference (dividedMicro c f θ θc) q*
        halfDifference (denominatorMap R θ*g) q∂pairingMeasure R) := by
  have hw := collision_weak_pairing hR (continuousExtension R f)
    (continuousExtension R (denominatorMap R θ*g))
  rw [restrictCube_extension,restrictCube_extension] at hw
  rw [hw]
  change c*(∫q,density (continuousExtension R f)
    (continuousExtension R (denominatorMap R θ*g)) q∂pairingMeasure R)=_
  rw [←integral_const_mul,←integral_neg]
  exact integral_congr_ae (weak_density_identity c f g hf hθ hθc)

theorem original_scaled_entropy_square {R : ℝ} (c : ℝ)
    (f : C(cube R,ℝ)) (hf : ∀ k,f k≠0) {θ θc : Parameter}
    (hθ : θ∈positiveDomain R) (hθc : θc∈positiveDomain R) :
    c^2*cubeProduction R f=
      ∫q,fullMobility f q*halfDifference (dividedMicro c f θ θc) q^2∂pairingMeasure R := by
  change c^2*(∫q,productionDensity (continuousExtension R f) q∂pairingMeasure R)=_
  rw [←integral_const_mul]
  exact integral_congr_ae (entropy_density_identity c f hf hθ hθc)

end
end Resonance.ActualMicroscopicCurrent
