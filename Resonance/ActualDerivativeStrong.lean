import Resonance.JointCornerStrong
import Resonance.ActualLocalizedOffDiagonal

/-! The original full cubic derivative perturbation, including its
entire diagonal, converges strongly in the single geometric marginal
space under bulk convergence and bounded corner values. Positivity of
the complete perturbed diagonal is not asserted here. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.ActualDerivativeStrong
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm JointWeightComparison
open FreeTransport FiberContinuity ContinuousCollisionPerturbation
open ActualLocalizedOffDiagonal LocalizedDerivativeCoefficients
open JointCornerStrong QuartetCoefficientLocalization LpOperators
set_option maxHeartbeats 2600000

def pairReader (R : ℝ) {b : FourMomenta→ℝ}
    (hb : MemLp b ∞ (jointMeasure R unitParameter)) (i j : Fin 4) :
    H R unitParameter →L[ℝ] H R unitParameter :=
  (pullback R unitParameter j).toContinuousLinearMap.adjoint.comp
    ((multiplyCLM hb).comp (pullback R unitParameter i).toContinuousLinearMap)

theorem pairReader_integrable (R : ℝ) {b : FourMomenta→ℝ}
    (hb : MemLp b ∞ (jointMeasure R unitParameter)) (i j : Fin 4)
    (u v : H R unitParameter) :
    Integrable (fun q=>b q*u (q i)*v (q j)) (jointMeasure R unitParameter) := by
  apply ((Lp.memLp (multiplyCLM hb (pullback R unitParameter i u))).integrable_mul
    (Lp.memLp (pullback R unitParameter j v))).congr
  filter_upwards [multiply_ae hb (pullback R unitParameter i u),
    pullback_ae R unitParameter i u,pullback_ae R unitParameter j v] with q hbq hu hv
  change multiplyCLM hb (pullback R unitParameter i u) q=(pullback R unitParameter i u) q*b q at hbq
  change (multiplyCLM hb (pullback R unitParameter i u)) q*(pullback R unitParameter j v) q=_
  rw [hbq,hu,hv]
  ring

theorem pairReader_pairing (R : ℝ) {b : FourMomenta→ℝ}
    (hb : MemLp b ∞ (jointMeasure R unitParameter)) (i j : Fin 4)
    (u v : H R unitParameter) :
    inner ℝ v (pairReader R hb i j u)=∫q,b q*u (q i)*v (q j)∂jointMeasure R unitParameter := by
  rw [show inner ℝ v (pairReader R hb i j u)=
    inner ℝ (pullback R unitParameter j v) (multiplyCLM hb (pullback R unitParameter i u)) from
    ContinuousLinearMap.adjoint_inner_right (pullback R unitParameter j).toContinuousLinearMap v _]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae hb (pullback R unitParameter i u),
    pullback_ae R unitParameter i u,pullback_ae R unitParameter j v] with q hbq hu hv
  change multiplyCLM hb (pullback R unitParameter i u) q=(pullback R unitParameter i u) q*b q at hbq
  change (multiplyCLM hb (pullback R unitParameter i u)) q*(pullback R unitParameter j v) q=_
  rw [hbq,hu,hv]
  ring

theorem actual_coefficient_memLp {R : ℝ} (_hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) (i j : Fin 4) :
    MemLp (coefficientAt R f N i j) ∞ (jointMeasure R unitParameter) := by
  apply memLp_top_of_bound (coefficientAt_measurable R f N i j).aestronglyMeasurable
    ((6*M^2/m)*(2*M))
  rw [unit_joint R]
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  have hfv (l:Fin 4) : |continuousExtension R f (q l)| ≤ M := by
    rw [continuousExtension_eq R f ⟨q l,hq.1 l⟩]
    exact hf _
  have hNv (l:Fin 4) : m ≤ continuousExtension R N (q l) ∧ |continuousExtension R N (q l)| ≤ M := by
    rw [continuousExtension_eq R N ⟨q l,hq.1 l⟩]
    exact hN _
  have hd (l:Fin 4) : |continuousExtension R f (q l)-continuousExtension R N (q l)| ≤ 2*M :=
    (abs_sub _ _).trans (by linarith [hfv l,(hNv l).2])
  exact relativeCoefficient_bound _ _ hm hM (by positivity) hfv hNv hd i j

def actualPair {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) (i j : Fin 4) :
    H R unitParameter →L[ℝ] H R unitParameter :=
  pairReader R (actual_coefficient_memLp hR f N hm hM hf hN i j) i j

/-- The coefficient family is the actual twelve-parent cubic derivative
formed from f and N on one original quartet. All sixteen observed pairs,
including the four diagonal pairs, are allowed. -/
theorem actual_pair_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f : I→CubeFunction R) (N : CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0))
    (i j : Fin 4) (u : H R unitParameter) :
    Tendsto (fun s=>actualPair hR (f s) N hm hM (hf s) hN i j u) l (𝓝 0) := by
  let b (s:I):FourMomenta→ℝ:=coefficientAt R (f s) N i j
  let hb (s:I):MemLp (b s) ∞ (jointMeasure R unitParameter):=
    actual_coefficient_memLp hR (f s) N hm hM (hf s) hN i j
  let κ' (s:I):ℝ:=(6*M^2/m)*|κ s|
  have hkp : ∀s,0 ≤ κ' s:=fun _=>by dsimp [κ']; positivity
  have henv : ∀s,∀ᵐq∂jointMeasure R unitParameter,
      |b s q| ≤ envelope R |κ' s| (12*M^3/m) (η s) q := by
    intro s
    rw [abs_of_nonneg (hkp s)]
    exact actual_coefficient_envelope hR (f s) N hm hM (abs_nonneg _) (hf s) hN (hbulk s) i j
  have hk' : Tendsto κ' l (𝓝 0) := by
    simpa only [abs_zero,mul_zero] using (hκ.abs).const_mul (6*M^2/m)
  have hh:=actual_joint_envelope_strong hR unitParameter l b hb κ' η
    (show 0 ≤ 12*M^3/m by positivity) henv hk' hη (pullback R unitParameter i u)
  have hr:=((pullback R unitParameter j).toContinuousLinearMap.adjoint.continuous.tendsto 0).comp hh
  simpa only [map_zero] using hr

def fullReader {R : ℝ} (hR : 0 < R) (f N : CubeFunction R)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀k,|f k| ≤ M) (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) :
    H R unitParameter →L[ℝ] H R unitParameter :=
  ∑i:Fin 4,∑j:Fin 4,actualPair hR f N hm hM hf hN i j

theorem actual_full_reader_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f : I→CubeFunction R) (N : CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀k,m ≤ N k ∧ |N k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (u : H R unitParameter) :
    Tendsto (fun s=>fullReader hR (f s) N hm hM (hf s) hN u) l (𝓝 0) := by
  have hh:=tendsto_finset_sum (Finset.univ:Finset (Fin 4)) (fun i _=>
    tendsto_finset_sum (Finset.univ:Finset (Fin 4)) (fun j _=>
      actual_pair_strong hR l f N hm hM hf hN κ η hbulk hκ hη i j u))
  simpa only [Finset.sum_const_zero,fullReader,ContinuousLinearMap.sum_apply] using hh

/-- All backgrounds share the actual unit joint measure. No convergence
of N_s is needed for this derivative-difference estimate; the common
positive amplitude bounds suffice. -/
theorem actual_pair_family_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f N : I→CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀s k,m ≤ N s k ∧ |N s k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N s k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0))
    (i j : Fin 4) (u : H R unitParameter) :
    Tendsto (fun s=>actualPair hR (f s) (N s) hm hM (hf s) (hN s) i j u) l (𝓝 0) := by
  let b (s:I):FourMomenta→ℝ:=coefficientAt R (f s) (N s) i j
  let hb (s:I):MemLp (b s) ∞ (jointMeasure R unitParameter):=
    actual_coefficient_memLp hR (f s) (N s) hm hM (hf s) (hN s) i j
  let κ' (s:I):ℝ:=(6*M^2/m)*|κ s|
  have hkp : ∀s,0 ≤ κ' s:=fun _=>by dsimp [κ']; positivity
  have henv : ∀s,∀ᵐq∂jointMeasure R unitParameter,
      |b s q| ≤ envelope R |κ' s| (12*M^3/m) (η s) q := by
    intro s
    rw [abs_of_nonneg (hkp s)]
    exact actual_coefficient_envelope hR (f s) (N s) hm hM (abs_nonneg _)
      (hf s) (hN s) (hbulk s) i j
  have hk' : Tendsto κ' l (𝓝 0) := by
    simpa only [abs_zero,mul_zero] using (hκ.abs).const_mul (6*M^2/m)
  have hh:=actual_joint_envelope_strong hR unitParameter l b hb κ' η
    (show 0 ≤ 12*M^3/m by positivity) henv hk' hη (pullback R unitParameter i u)
  have hr:=((pullback R unitParameter j).toContinuousLinearMap.adjoint.continuous.tendsto 0).comp hh
  simpa only [map_zero] using hr

theorem actual_full_family_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (l : Filter I) (f N : I→CubeFunction R) {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hf : ∀s k,|f s k| ≤ M)
    (hN : ∀s k,m ≤ N s k ∧ |N s k| ≤ M) (κ η : I→ℝ)
    (hbulk : ∀s (k:MomentumDomain R),η s < CornerFrequencyBounds.cornerDepth R k → |f s k-N s k| ≤ |κ s|)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (u : H R unitParameter) :
    Tendsto (fun s=>fullReader hR (f s) (N s) hm hM (hf s) (hN s) u) l (𝓝 0) := by
  have hh:=tendsto_finset_sum (Finset.univ:Finset (Fin 4)) (fun i _=>
    tendsto_finset_sum (Finset.univ:Finset (Fin 4)) (fun j _=>
      actual_pair_family_strong hR l f N hm hM hf hN κ η hbulk hκ hη i j u))
  simpa only [Finset.sum_const_zero,fullReader,ContinuousLinearMap.sum_apply] using hh

end
end Resonance.ActualDerivativeStrong
