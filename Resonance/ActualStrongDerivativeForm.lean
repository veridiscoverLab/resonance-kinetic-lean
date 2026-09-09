import Resonance.ActualDerivativeStrong

/-! The strongly convergent reader is identified with the actual C(D)
Frechet collision derivative and with the physical fixed Hν form. All
four source parents, all four test parents and the factor 1/4 remain. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.ActualStrongDerivativeForm
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm JointWeightComparison
open FreeTransport FiberContinuity ContinuousCollisionPerturbation
open ContinuousWeightedEnergy (toWeighted)
open ActualLocalizedOffDiagonal LocalizedDerivativeCoefficients ActualDerivativeStrong
set_option maxHeartbeats 2600000

theorem full_reader_pairing {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M)
    (u v : H R unitParameter) :
    inner ℝ v (fullReader hR f N hm hM hf hN u)=
      ∫q,∑i:Fin 4,∑j:Fin 4,coefficientAt R f N i j q*u (q i)*v (q j)∂jointMeasure R unitParameter := by
  have hI (i j:Fin 4) := pairReader_integrable R
    (actual_coefficient_memLp hR f N hm hM hf hN i j) i j u v
  have he : (∫q,∑i:Fin 4,∑j:Fin 4,coefficientAt R f N i j q*u (q i)*v (q j)∂jointMeasure R unitParameter)=
      ∑i:Fin 4,∑j:Fin 4,∫q,coefficientAt R f N i j q*u (q i)*v (q j)∂jointMeasure R unitParameter := by
    rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>hI i j))]
    exact Finset.sum_congr rfl (fun i _=>integral_finset_sum _ (fun j _=>hI i j))
  rw [he]
  simp only [fullReader,ContinuousLinearMap.sum_apply,inner_sum,actualPair,pairReader_pairing]

def referenceReader {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) :
    ReferenceFrequencySpace.Space R →L[ℝ] ReferenceFrequencySpace.Space R :=
  (toUnit hR).adjoint.comp ((fullReader hR f N hm hM hf hN).comp (toUnit hR))

/-- Exact original collision form, not only an abstract kernel reader. -/
theorem actual_continuous_reference_pairing {R : ℝ} (hR : 0 < R) (f N u : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) :
    inner ℝ (toWeighted hR u) (referenceReader hR f N hm hM hf hN (toWeighted hR u))=
      ContinuousCollisionMoments.cubeIntegral R ((u*ContinuousCollisionForm.inverseCube N
        (fun k=>(hm.trans_le (hN k).1).ne'))*
        (fderiv ℝ (collisionMap R hR.le) f (N*u)-fderiv ℝ (collisionMap R hR.le) N (N*u))) := by
  rw [show inner ℝ (toWeighted hR u) (referenceReader hR f N hm hM hf hN (toWeighted hR u))=
    inner ℝ (toUnit hR (toWeighted hR u))
      (fullReader hR f N hm hM hf hN (toUnit hR (toWeighted hR u))) from
    ContinuousLinearMap.adjoint_inner_right (toUnit hR) (toWeighted hR u) _]
  rw [full_reader_pairing,actual_perturbation_integral]
  rw [←unit_joint R]
  apply integral_congr_ae
  have ha : ∀ᵐq∂jointMeasure R unitParameter,∀i:Fin 4,
      toUnit hR (toWeighted hR u) (q i)=continuousExtension R u (q i) :=
    ae_all_iff.mpr (fun i=>(all_legs_preserve R unitParameter i).quasiMeasurePreserving.ae_eq
      (toUnit_ae hR u))
  filter_upwards [ha] with q hq
  simp_rw [hq]
  exact (complete_parent_pair_identity _ _ _).symm

/-- Strong convergence in the same physical weighted space as the
coframe energy. No step assumes the inverse frequency is bounded. -/
theorem actual_reference_reader_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f : I→CubeFunction R) (N : CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (u : ReferenceFrequencySpace.Space R) :
    Tendsto (fun s=>referenceReader hR (f s) N hm hM (hf s) hN u) l (𝓝 0) := by
  have hh:=actual_full_reader_strong hR l f N hm hM hf hN κ η hbulk hκ hη (toUnit hR u)
  have hr:=((toUnit hR).adjoint.continuous.tendsto 0).comp hh
  simpa only [map_zero] using hr

/-- The fixed-test limit is read back to the actual continuous collision
map. It does not permit a varying unbounded energy vector. -/
theorem actual_fixed_test_limit {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f : I→CubeFunction R) (N u : CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun s=>ContinuousCollisionMoments.cubeIntegral R ((u*ContinuousCollisionForm.inverseCube N
      (fun k=>(hm.trans_le (hN k).1).ne'))*
      (fderiv ℝ (collisionMap R hR.le) (f s) (N*u)-fderiv ℝ (collisionMap R hR.le) N (N*u)))) l (𝓝 0) := by
  have hh:=(tendsto_const_nhds (x:=toWeighted hR u)).inner (𝕜:=ℝ)
    (actual_reference_reader_strong hR l f N hm hM hf hN κ η hbulk hκ hη (toWeighted hR u))
  simpa only [inner_zero_right,actual_continuous_reference_pairing] using hh

theorem actual_reference_family_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f N : I→CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀s k,m ≤ N s k ∧ |N s k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N s k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (u : ReferenceFrequencySpace.Space R) :
    Tendsto (fun s=>referenceReader hR (f s) (N s) hm hM (hf s) (hN s) u) l (𝓝 0) := by
  have hh:=actual_full_family_strong hR l f N hm hM hf hN κ η hbulk hκ hη (toUnit hR u)
  have hr:=((toUnit hR).adjoint.continuous.tendsto 0).comp hh
  simpa only [map_zero] using hr

/-- The same fixed physical test reads every member of a moving positive
background family, with the actual N_s in both normalization factors. -/
theorem actual_fixed_test_family_limit {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f N : I→CubeFunction R) (u : CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀s k,m ≤ N s k ∧ |N s k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N s k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun s=>ContinuousCollisionMoments.cubeIntegral R ((u*ContinuousCollisionForm.inverseCube (N s)
      (fun k=>(hm.trans_le (hN s k).1).ne'))*
      (fderiv ℝ (collisionMap R hR.le) (f s) (N s*u)-fderiv ℝ (collisionMap R hR.le) (N s) (N s*u)))) l (𝓝 0) := by
  have hh:=(tendsto_const_nhds (x:=toWeighted hR u)).inner (𝕜:=ℝ)
    (actual_reference_family_strong hR l f N hm hM hf hN κ η hbulk hκ hη (toWeighted hR u))
  simpa only [inner_zero_right,actual_continuous_reference_pairing] using hh

end
end Resonance.ActualStrongDerivativeForm
