import Resonance.JetMildEquation

/-! Actual separate spatial derivative seminorms, defined by the common
translation orbit into the original phase-space C norm. Transport preserves
each order; the complete mild equation implies its integrated norm bound. -/
open Set MeasureTheory
open scoped Interval
namespace Resonance.JetSeminorm
noncomputable section
open JetCollision SpatialChainRule SpatialTranslationOrbit FreeTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

abbrev Tensor (R : ℝ) (n : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n => RealPosition) (Distribution R)

def orbitDerivativeLinear (R : ℝ) (n : ℕ) (hn : n ≤ 3) : Space R →ₗ[ℝ] Tensor R n where
  toFun p := iteratedFDeriv ℝ n (distributionOrbit (readback p)) 0
  map_add' p q := by
    have he : distributionOrbit (readback (p+q)) =
        distributionOrbit (readback p) + distributionOrbit (readback q) := by
      funext x
      ext z
      rfl
    rw [he]
    exact iteratedFDeriv_add_apply
      ((distributionOrbit_contDiff p).of_le (by exact_mod_cast hn)).contDiffAt
      ((distributionOrbit_contDiff q).of_le (by exact_mod_cast hn)).contDiffAt
  map_smul' a p := by
    have he : distributionOrbit (readback (a • p)) = a • distributionOrbit (readback p) := by
      funext x
      ext z
      rfl
    rw [he]
    exact iteratedFDeriv_const_smul_apply
      ((distributionOrbit_contDiff p).of_le (by exact_mod_cast hn)).contDiffAt

theorem orbitDerivativeLinear_bound (R : ℝ) (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    ‖orbitDerivativeLinear R n hn p‖ ≤ ‖p‖ :=
  distributionOrbit_derivative_norm p 0 hn

def orbitDerivative (R : ℝ) (n : ℕ) (hn : n ≤ 3) : Space R →L[ℝ] Tensor R n :=
  (orbitDerivativeLinear R n hn).mkContinuous 1
    (fun p => by simpa only [one_mul] using orbitDerivativeLinear_bound R n hn p)

theorem orbitDerivative_actual (R : ℝ) (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    orbitDerivative R n hn p = iteratedFDeriv ℝ n (distributionOrbit (readback p)) 0 := rfl

def spatialSeminorm (R : ℝ) (n : ℕ) (hn : n ≤ 3) (p : Space R) : ℝ :=
  ‖orbitDerivative R n hn p‖

theorem spatialSeminorm_nonnegative (R : ℝ) (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    0 ≤ spatialSeminorm R n hn p := norm_nonneg _

theorem spatialSeminorm_le_norm (R : ℝ) (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    spatialSeminorm R n hn p ≤ ‖p‖ := orbitDerivativeLinear_bound R n hn p

theorem spatialSeminorm_continuous (R : ℝ) (n : ℕ) (hn : n ≤ 3) :
    Continuous (spatialSeminorm R n hn) := (orbitDerivative R n hn).continuous.norm

theorem spatialSeminorm_zero (R : ℝ) (p : Space R) :
    spatialSeminorm R 0 (by omega) p = ‖readback p‖ := by
  change ‖iteratedFDeriv ℝ 0 (distributionOrbit (readback p)) 0‖ = _
  rw [norm_iteratedFDeriv_zero]
  congr 1
  ext z
  change readback p (torusQuotient 0+z.1,z.2)=readback p z
  have hz : torusQuotient (0 : RealPosition) = (0 : SpatialTorus) := by
    funext i
    simp [torusQuotient]
  rw [hz,zero_add]

theorem norm_le_sum_spatialSeminorm (R : ℝ) (p : Space R) :
    ‖p‖ ≤ ∑ n : Fin 4,spatialSeminorm R n.val (by omega) p :=
  JetTransport.norm_le_orbit_sum R p

theorem actual_derivative_norm_le_spatialSeminorm (R : ℝ) (n : ℕ) (hn : n ≤ 3)
    (p : Space R) (x : RealPosition) :
    ‖iteratedFDeriv ℝ n (realLift (readback p)) x‖ ≤ spatialSeminorm R n hn p :=
  JetTransport.derivative_norm_le_orbit_zero R p x hn

theorem orbitDerivative_transport (R t : ℝ) (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    orbitDerivative R n hn (JetTransport.map R t p) =
      (transportCLM R t).compContinuousMultilinearMap (orbitDerivative R n hn p) := by
  have he : distributionOrbit (readback (JetTransport.map R t p)) =
      transportCLM R t ∘ distributionOrbit (readback p) := by
    funext x
    rw [JetTransport.map_readback,distributionOrbit_transport]
    rfl
  simp only [orbitDerivative_actual,he]
  exact (transportCLM R t).iteratedFDeriv_comp_left
    (f := distributionOrbit (readback p)) (x := (0 : RealPosition)) (i := n)
    (distributionOrbit_contDiff p).contDiffAt (by exact_mod_cast hn)

theorem spatialSeminorm_transport (R t : ℝ) (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    spatialSeminorm R n hn (JetTransport.map R t p) = spatialSeminorm R n hn p := by
  unfold spatialSeminorm
  rw [orbitDerivative_transport]
  exact (transportIsometry R t).norm_compContinuousMultilinearMap (orbitDerivative R n hn p)

theorem spatialSeminorm_smul (R : ℝ) (n : ℕ) (hn : n ≤ 3) (a : ℝ) (p : Space R) :
    spatialSeminorm R n hn (a • p) = |a| * spatialSeminorm R n hn p := by
  unfold spatialSeminorm
  rw [map_smul,norm_smul,Real.norm_eq_abs]

theorem source_spatialSeminorm {R : ℝ} (hR : 0 ≤ R) (c t s : ℝ)
    (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    spatialSeminorm R n hn (JetMildEquation.transportedSource R hR c t s p) =
      |c| * spatialSeminorm R n hn (JetCollision.collision R hR p) := by
  rw [JetMildEquation.transportedSource,spatialSeminorm_smul,spatialSeminorm_transport]

theorem actual_mild_seminorm_bound {R : ℝ} (hR : 0 ≤ R) (c t : ℝ) (ht : 0 ≤ t)
    (n : ℕ) (hn : n ≤ 3) (p₀ : Space R) (p : ℝ → Space R) (hp : Continuous p)
    (he : readback (p t) = transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t,c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s)))) :
    spatialSeminorm R n hn (p t) ≤ spatialSeminorm R n hn p₀ +
      |c| * ∫ s in (0 : ℝ)..t,spatialSeminorm R n hn (JetCollision.collision R hR (p s)) := by
  have hd := JetMildEquation.actual_mild_linear_extraction hR c t p₀ p hp
    (orbitDerivative R n hn) he
  unfold spatialSeminorm at ⊢
  rw [hd]
  apply (norm_add_le _ _).trans
  have hi := intervalIntegral.norm_integral_le_integral_norm (μ := volume) ht
    (f := fun s => orbitDerivative R n hn (JetMildEquation.transportedSource R hR c t s (p s)))
  have hsource : (fun s => ‖orbitDerivative R n hn
      (JetMildEquation.transportedSource R hR c t s (p s))‖) =
      fun s => |c| * spatialSeminorm R n hn (JetCollision.collision R hR (p s)) := by
    funext s
    exact source_spatialSeminorm hR c t s n hn (p s)
  rw [hsource,intervalIntegral.integral_const_mul] at hi
  exact add_le_add (spatialSeminorm_transport R t n hn p₀).le hi

end
end Resonance.JetSeminorm

#check Resonance.JetSeminorm.orbitDerivativeLinear_bound
#print axioms Resonance.JetSeminorm.orbitDerivativeLinear_bound
#check Resonance.JetSeminorm.orbitDerivative_actual
#print axioms Resonance.JetSeminorm.orbitDerivative_actual
#check Resonance.JetSeminorm.spatialSeminorm_nonnegative
#print axioms Resonance.JetSeminorm.spatialSeminorm_nonnegative
#check Resonance.JetSeminorm.spatialSeminorm_le_norm
#print axioms Resonance.JetSeminorm.spatialSeminorm_le_norm
#check Resonance.JetSeminorm.spatialSeminorm_continuous
#print axioms Resonance.JetSeminorm.spatialSeminorm_continuous
#check Resonance.JetSeminorm.spatialSeminorm_zero
#print axioms Resonance.JetSeminorm.spatialSeminorm_zero
#check Resonance.JetSeminorm.norm_le_sum_spatialSeminorm
#print axioms Resonance.JetSeminorm.norm_le_sum_spatialSeminorm
#check Resonance.JetSeminorm.actual_derivative_norm_le_spatialSeminorm
#print axioms Resonance.JetSeminorm.actual_derivative_norm_le_spatialSeminorm
#check Resonance.JetSeminorm.orbitDerivative_transport
#print axioms Resonance.JetSeminorm.orbitDerivative_transport
#check Resonance.JetSeminorm.spatialSeminorm_transport
#print axioms Resonance.JetSeminorm.spatialSeminorm_transport
#check Resonance.JetSeminorm.spatialSeminorm_smul
#print axioms Resonance.JetSeminorm.spatialSeminorm_smul
#check Resonance.JetSeminorm.source_spatialSeminorm
#print axioms Resonance.JetSeminorm.source_spatialSeminorm
#check Resonance.JetSeminorm.actual_mild_seminorm_bound
#print axioms Resonance.JetSeminorm.actual_mild_seminorm_bound
