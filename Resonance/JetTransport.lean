import Resonance.JetCollision
import Resonance.SpatialTranslationOrbit
import Resonance.FiniteTensorContinuity

/-! Free transport on the original closed compatible jet space. -/
open Set Function Filter
open scoped Topology ContDiff
namespace Resonance.JetTransport
noncomputable section
open FreeTransport SpatialChainRule SpatialJetSpace SpatialJetDescent
open SpatialTranslationOrbit JetCollision
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

theorem continuous_action_of_isometries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ℝ → E →L[ℝ] E) (hn : ∀ t p,‖S t p‖=‖p‖)
    (hc : ∀ p,Continuous (fun t => S t p)) : Continuous (fun q : ℝ × E => S q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t,p⟩
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun q : ℝ × E => ‖q.2-p‖) (𝓝 (t,p)) (𝓝 0) := by
    have h : Continuous (fun q : ℝ × E => q.2-p) := continuous_snd.sub continuous_const
    simpa using h.norm.continuousAt.tendsto (x := (t,p))
  have h2 : Tendsto (fun q : ℝ × E => ‖S q.1 p-S t p‖) (𝓝 (t,p)) (𝓝 0) := by
    have h : Continuous (fun q : ℝ × E => S q.1 p-S t p) :=
      ((hc p).comp continuous_fst).sub continuous_const
    simpa using h.norm.continuousAt.tendsto (x := (t,p))
  have hsum : Tendsto (fun q : ℝ × E => ‖q.2-p‖+‖S q.1 p-S t p‖)
      (𝓝 (t,p)) (𝓝 0) := by simpa using h1.add h2
  apply squeeze_zero (fun q : ℝ × E => norm_nonneg (S q.1 q.2-S t p)) _ hsum
  intro q
  calc
    ‖S q.1 q.2-S t p‖≤‖S q.1 q.2-S q.1 p‖+‖S q.1 p-S t p‖ := by
      simpa only [dist_eq_norm] using dist_triangle (S q.1 q.2) (S q.1 p) (S t p)
    _=_ := by rw [← map_sub,hn]

instance tensorNormed (R : ℝ) (n : ℕ) : NormedAddCommGroup
    (ContinuousMultilinearMap ℝ (fun _ : Fin n => RealPosition) (Distribution R)) := inferInstance
instance tensorSpace (R : ℝ) (n : ℕ) : NormedSpace ℝ
    (ContinuousMultilinearMap ℝ (fun _ : Fin n => RealPosition) (Distribution R)) := inferInstance

def map (R t : ℝ) (p : Space R) : Space R :=
  jetOfDistribution (transport R t (readback p)) (transport_realLift_contDiff t p)

theorem map_readback (R t : ℝ) (p : Space R) :
    readback (map R t p)=transport R t (readback p) := jetOfDistribution_readback _ _

theorem map_add (R t : ℝ) (p q : Space R) : map R t (p+q)=map R t p+map R t q := by
  apply readback_injective R
  simp only [readback_add,map_readback,transport_add]

theorem map_smul (R t s : ℝ) (p : Space R) : map R t (s • p)=s • map R t p := by
  apply readback_injective R
  simp only [readback_smul,map_readback,transport_smul]

theorem readAtTransport_norm_le (R t : ℝ) :
    ‖(zeroEvaluationCLM R).comp (transportCLM R t)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖SpatialCollision.momentumSection (transport R t f) 0‖≤1*‖f‖
  rw [one_mul]
  exact (SpatialCollision.momentumSection_norm_le _ _).trans (transport_norm_le R t f)

theorem map_iterated_derivative_norm (R t : ℝ) (p : Space R) (x : RealPosition)
    {n : ℕ} (hn : n≤3) :
    ‖iteratedFDeriv ℝ n (realLift (readback (map R t p))) x‖≤‖p‖ := by
  rw [map_readback,realLift_transport_orbit]
  have h := ((zeroEvaluationCLM R).comp (transportCLM R t)).norm_iteratedFDeriv_comp_left
    (x := x) (n := n) (distributionOrbit_contDiff p).contDiffAt (by exact_mod_cast hn)
  exact h.trans ((mul_le_mul_of_nonneg_right (readAtTransport_norm_le R t) (norm_nonneg _)).trans
    (by simpa only [one_mul] using distributionOrbit_derivative_norm p x hn))

theorem map_norm_le (R t : ℝ) (p : Space R) : ‖map R t p‖≤‖p‖ := by
  apply (jet_norm_le_iff (norm_nonneg p) (map R t p)).mpr
  intro x
  have h0 := map_iterated_derivative_norm R t p x (n := 0) (by norm_num)
  have h1 := map_iterated_derivative_norm R t p x (n := 1) (by norm_num)
  have h2 := map_iterated_derivative_norm R t p x (n := 2) (by norm_num)
  have h3 := map_iterated_derivative_norm R t p x (n := 3) (by norm_num)
  rw [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at h2
  rw [← norm_iteratedFDeriv_fderiv (n := 2),← norm_iteratedFDeriv_fderiv (n := 1),
    norm_iteratedFDeriv_one] at h3
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using h0,
    by simpa only [norm_iteratedFDeriv_one] using h1,h2,h3⟩

theorem map_zero_time (R : ℝ) (p : Space R) : map R 0 p=p := by
  apply readback_injective R
  rw [map_readback,transport_zero]

theorem map_add_time (R s t : ℝ) (p : Space R) :
    map R s (map R t p)=map R (s+t) p := by
  apply readback_injective R
  simp only [map_readback,transport_add_time]

theorem map_norm (R t : ℝ) (p : Space R) : ‖map R t p‖=‖p‖ := by
  apply le_antisymm (map_norm_le R t p)
  have h := map_norm_le R (-t) (map R t p)
  simpa only [map_add_time,neg_add_cancel,map_zero_time] using h

def linear (R t : ℝ) : Space R →ₗ[ℝ] Space R where
  toFun := map R t
  map_add' := map_add R t
  map_smul' := map_smul R t

def isometry (R t : ℝ) : Space R →ₗᵢ[ℝ] Space R where
  toLinearMap := linear R t
  norm_map' := map_norm R t

def operator (R t : ℝ) : Space R →L[ℝ] Space R :=
  (isometry R t).toContinuousLinearMap

theorem operator_readback (R t : ℝ) (p : Space R) :
    readback (operator R t p)=transportCLM R t (readback p) := map_readback R t p

def evaluationLinear (R : ℝ) (X : SpatialTorus) : Distribution R →ₗ[ℝ] V0 R where
  toFun f := SpatialCollision.momentumSection f X
  map_add' a b := by ext k; rfl
  map_smul' s a := by ext k; rfl

def evaluationCLM (R : ℝ) (X : SpatialTorus) : Distribution R →L[ℝ] V0 R :=
  (evaluationLinear R X).mkContinuous 1 (fun f => by
    simpa only [one_mul] using SpatialCollision.momentumSection_norm_le f X)

theorem evaluationCLM_norm_le (R : ℝ) (X : SpatialTorus) : ‖evaluationCLM R X‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using SpatialCollision.momentumSection_norm_le f X

theorem derivative_norm_le_orbit_zero (R : ℝ) (p : Space R) (x : RealPosition)
    {n : ℕ} (hn : n≤3) :
    ‖iteratedFDeriv ℝ n (realLift (readback p)) x‖≤
      ‖iteratedFDeriv ℝ n (distributionOrbit (readback p)) 0‖ := by
  have he : (evaluationCLM R (torusQuotient x)) ∘ distributionOrbit (readback p)=
      fun z => realLift (readback p) (z+x) := by
    funext z
    apply ContinuousMap.ext
    intro k
    change readback p (torusQuotient z+torusQuotient x,k)=readback p (torusQuotient (z+x),k)
    rw [torusQuotient_add]
  have hc : ContDiff ℝ 3 (distributionOrbit (readback p)) := distributionOrbit_contDiff p
  have h := (evaluationCLM R (torusQuotient x)).norm_iteratedFDeriv_comp_left
    (f := distributionOrbit (readback p)) (x := (0 : RealPosition)) (n := n) hc.contDiffAt
    (by exact_mod_cast hn)
  rw [he,iteratedFDeriv_comp_add_right,zero_add] at h
  have hb := mul_le_mul_of_nonneg_right (evaluationCLM_norm_le R (torusQuotient x))
    (norm_nonneg (iteratedFDeriv ℝ n (distributionOrbit (readback p)) 0))
  exact h.trans (by simpa only [one_mul] using hb)

theorem norm_le_orbit_sum (R : ℝ) (p : Space R) :
    ‖p‖≤∑ n : Fin 4,‖iteratedFDeriv ℝ n.val (distributionOrbit (readback p)) 0‖ := by
  let M := ∑ n : Fin 4,‖iteratedFDeriv ℝ n.val (distributionOrbit (readback p)) 0‖
  have hM : 0≤M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply (jet_norm_le_iff hM p).mpr
  intro x
  have hb (n : Fin 4) : ‖iteratedFDeriv ℝ n.val (realLift (readback p)) x‖≤M := by
    apply (derivative_norm_le_orbit_zero R p x (by omega)).trans
    exact Finset.single_le_sum
      (fun m _ => norm_nonneg (iteratedFDeriv ℝ m.val (distributionOrbit (readback p)) 0))
      (Finset.mem_univ n)
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  change ‖iteratedFDeriv ℝ 0 (realLift (readback p)) x‖≤M at h0
  change ‖iteratedFDeriv ℝ 1 (realLift (readback p)) x‖≤M at h1
  change ‖iteratedFDeriv ℝ 2 (realLift (readback p)) x‖≤M at h2
  change ‖iteratedFDeriv ℝ 3 (realLift (readback p)) x‖≤M at h3
  rw [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at h2
  rw [← norm_iteratedFDeriv_fderiv (n := 2),← norm_iteratedFDeriv_fderiv (n := 1),
    norm_iteratedFDeriv_one] at h3
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using h0,
    by simpa only [norm_iteratedFDeriv_one] using h1,h2,h3⟩

theorem readback_sub (R : ℝ) (p q : Space R) : readback (p-q)=readback p-readback q := by
  ext z
  rfl

theorem map_difference_orbit (R t s : ℝ) (p : Space R) :
    distributionOrbit (readback (map R t p-map R s p))=
      (transportCLM R t-transportCLM R s) ∘ distributionOrbit (readback p) := by
  funext x
  rw [readback_sub,map_readback,map_readback]
  change distributionOrbit (transport R t (readback p)) x-
    distributionOrbit (transport R s (readback p)) x=_
  rw [distributionOrbit_transport,distributionOrbit_transport]
  rfl

theorem map_difference_orbit_derivative (R t s : ℝ) (p : Space R) {n : ℕ} (hn : n≤3) :
    iteratedFDeriv ℝ n (distributionOrbit (readback (map R t p-map R s p))) 0=
      (transportCLM R t).compContinuousMultilinearMap (iteratedFDeriv ℝ n (distributionOrbit (readback p)) 0)-
      (transportCLM R s).compContinuousMultilinearMap (iteratedFDeriv ℝ n (distributionOrbit (readback p)) 0) := by
  rw [map_difference_orbit]
  have hc : ContDiff ℝ 3 (distributionOrbit (readback p)) := distributionOrbit_contDiff p
  rw [(transportCLM R t-transportCLM R s).iteratedFDeriv_comp_left
    (f := distributionOrbit (readback p)) (x := (0 : RealPosition)) (i := n)
    hc.contDiffAt (by exact_mod_cast hn)]
  rfl

theorem map_strong_continuous (R : ℝ) (p : Space R) : Continuous (fun t : ℝ => map R t p) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  let A (n : Fin 4) := iteratedFDeriv ℝ n.val (distributionOrbit (readback p)) 0
  have hc (n : Fin 4) : Continuous (fun t : ℝ => (transportCLM R t).compContinuousMultilinearMap (A n)) :=
    FiniteTensorContinuity.continuous_postcomposition (transportCLM R)
      (transport_strong_continuous R) (A n)
  have hd : Continuous (fun t : ℝ => ∑ n : Fin 4,
      ‖(transportCLM R t).compContinuousMultilinearMap (A n)-
        (transportCLM R s).compContinuousMultilinearMap (A n)‖) :=
    continuous_finset_sum Finset.univ (fun n _ => by
      have hs : Continuous (fun _ : ℝ => (transportCLM R s).compContinuousMultilinearMap (A n)) := continuous_const
      exact ((hc n).sub hs).norm)
  have ht : Tendsto (fun t : ℝ => ∑ n : Fin 4,
      ‖(transportCLM R t).compContinuousMultilinearMap (A n)-
        (transportCLM R s).compContinuousMultilinearMap (A n)‖) (𝓝 s) (𝓝 0) := by
    simpa only [sub_self,norm_zero,Finset.sum_const_zero] using hd.continuousAt.tendsto (x := s)
  apply squeeze_zero (fun t => norm_nonneg (map R t p-map R s p)) _ ht
  intro t
  have h := norm_le_orbit_sum R (map R t p-map R s p)
  convert h using 1
  apply Finset.sum_congr rfl
  intro n _
  rw [map_difference_orbit_derivative R t s p (by omega)]

theorem map_joint_continuous (R : ℝ) : Continuous (fun q : ℝ × Space R => map R q.1 q.2) := by
  exact continuous_action_of_isometries (operator R) (map_norm R) (map_strong_continuous R)

end
end Resonance.JetTransport

#check Resonance.JetTransport.continuous_action_of_isometries
#check Resonance.JetTransport.map_readback
#check Resonance.JetTransport.map_add
#check Resonance.JetTransport.map_smul
#check Resonance.JetTransport.readAtTransport_norm_le
#check Resonance.JetTransport.map_iterated_derivative_norm
#check Resonance.JetTransport.map_norm_le
#check Resonance.JetTransport.map_zero_time
#check Resonance.JetTransport.map_add_time
#check Resonance.JetTransport.map_norm
#check Resonance.JetTransport.operator_readback
#check Resonance.JetTransport.evaluationCLM_norm_le
#check Resonance.JetTransport.derivative_norm_le_orbit_zero
#check Resonance.JetTransport.norm_le_orbit_sum
#check Resonance.JetTransport.readback_sub
#check Resonance.JetTransport.map_difference_orbit
#check Resonance.JetTransport.map_difference_orbit_derivative
#check Resonance.JetTransport.map_strong_continuous
#check Resonance.JetTransport.map_joint_continuous
#print axioms Resonance.JetTransport.continuous_action_of_isometries
#print axioms Resonance.JetTransport.map_readback
#print axioms Resonance.JetTransport.map_add
#print axioms Resonance.JetTransport.map_smul
#print axioms Resonance.JetTransport.readAtTransport_norm_le
#print axioms Resonance.JetTransport.map_iterated_derivative_norm
#print axioms Resonance.JetTransport.map_norm_le
#print axioms Resonance.JetTransport.map_zero_time
#print axioms Resonance.JetTransport.map_add_time
#print axioms Resonance.JetTransport.map_norm
#print axioms Resonance.JetTransport.operator_readback
#print axioms Resonance.JetTransport.evaluationCLM_norm_le
#print axioms Resonance.JetTransport.derivative_norm_le_orbit_zero
#print axioms Resonance.JetTransport.norm_le_orbit_sum
#print axioms Resonance.JetTransport.readback_sub
#print axioms Resonance.JetTransport.map_difference_orbit
#print axioms Resonance.JetTransport.map_difference_orbit_derivative
#print axioms Resonance.JetTransport.map_strong_continuous
#print axioms Resonance.JetTransport.map_joint_continuous
