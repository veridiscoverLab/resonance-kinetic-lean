import Resonance.ActualLocalizedOffDiagonal

/-! Complete actual derivative split and its corner-localized cross error.
The diagonal integral is retained exactly for the separate loss geometry. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.FullLocalizedDerivativeSplit
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity
open ContinuousCollisionPerturbation LocalizedDerivativeCoefficients ActualLocalizedOffDiagonal
open ContinuousWeightedEnergy (toWeighted)
open AllMarkedQuartetReaders JointWeightComparison
set_option maxHeartbeats 2200000

def crossTerm (R : ℝ) (f N u : CubeFunction R) (i j : Fin 4) (q : FourMomenta) : ℝ:=
  if i=j then 0 else pairDensity R f N u i j q

def offDensity (R : ℝ) (f N u : CubeFunction R) (q : FourMomenta) : ℝ:=
  ∑i:Fin 4,∑j:Fin 4,crossTerm R f N u i j q

def diagDensity (R : ℝ) (f N u : CubeFunction R) (q : FourMomenta) : ℝ:=
  ∑i:Fin 4,coefficientAt R f N i i q*(continuousExtension R u (q i))^2

theorem complete_actual_density_split (R : ℝ) (f N u : CubeFunction R) (q : FourMomenta) :
    perturbationDensity R f N u q=diagDensity R f N u q+offDensity R f N u q :=
  complete_diagonal_offdiagonal_identity _ _ _

/-- All cross parents, all four sharp flags, one original resonance
measure. The displayed constant is deliberately a coarse 16-term bound. -/
theorem actual_full_offdiagonal_estimate {R : ℝ} (hR : 0<R) (f N u : CubeFunction R)
    {m M κ η : ℝ} (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ)
    (hf : ∀k,|f k|≤M) (hN : ∀k,m≤N k ∧ |N k|≤M)
    (hbulk : ∀k:MomentumDomain R, η<CornerFrequencyBounds.cornerDepth R k → |f k-N k|≤κ) :
    Integrable (offDensity R f N u) (pairingMeasure R) ∧
    |∫q,offDensity R f N u q∂pairingMeasure R|≤
      (16*energyCost R m M κ η*‖toUnit hR‖^2)*‖toWeighted hR u‖^2 := by
  let B:=(energyCost R m M κ η*‖toUnit hR‖^2)*‖toWeighted hR u‖^2
  have hB:0≤B:=mul_nonneg (mul_nonneg (energyCost_nonnegative R η hm hM hκ) (sq_nonneg _)) (sq_nonneg _)
  have hdata (i j:Fin 4) : Integrable (crossTerm R f N u i j) (pairingMeasure R) ∧
      |∫q,crossTerm R f N u i j q∂pairingMeasure R|≤B := by
    by_cases hij:i=j
    · have ht : crossTerm R f N u i j=(fun _=>0) := by funext q; simp [crossTerm,hij]
      rw [ht]
      exact ⟨integrable_zero _ _ _,by simpa using hB⟩
    · have ht : crossTerm R f N u i j=pairDensity R f N u i j := by funext q; simp [crossTerm,hij]
      rw [ht]
      exact actual_offdiagonal_pair_bound hR f N u hm hM hκ hf hN hbulk i j hij
  have hi : Integrable (offDensity R f N u) (pairingMeasure R):=
    integrable_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>(hdata i j).1))
  refine ⟨hi,?_⟩
  have he : (∫q,offDensity R f N u q∂pairingMeasure R)=
      ∑i:Fin 4,∑j:Fin 4,∫q,crossTerm R f N u i j q∂pairingMeasure R := by
    change (∫q,∑i:Fin 4,∑j:Fin 4,crossTerm R f N u i j q∂pairingMeasure R)=_
    rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>(hdata i j).1))]
    exact Finset.sum_congr rfl (fun i _=>integral_finset_sum _ (fun j _=>(hdata i j).1))
  rw [he]
  calc
    _≤∑i:Fin 4,|∑j:Fin 4,∫q,crossTerm R f N u i j q∂pairingMeasure R|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑i:Fin 4,∑j:Fin 4,|∫q,crossTerm R f N u i j q∂pairingMeasure R|:=
      Finset.sum_le_sum (fun i _=>Finset.abs_sum_le_sum_abs _ _)
    _≤∑_i:Fin 4,∑_j:Fin 4,B:=Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>(hdata i j).2))
    _=_:=by simp [B]; ring

/-- No nonlinear or spectral positivity is hidden in the diagonal: it
remains the exact original coefficient integral, available to the actual
role-mass geometry. -/
theorem actual_complete_derivative_split {R : ℝ} (hR : 0<R) (f N u : CubeFunction R)
    {m M κ η : ℝ} (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ)
    (hf : ∀k,|f k|≤M) (hN : ∀k,m≤N k ∧ |N k|≤M)
    (hbulk : ∀k:MomentumDomain R, η<CornerFrequencyBounds.cornerDepth R k → |f k-N k|≤κ) :
    Integrable (diagDensity R f N u) (pairingMeasure R) ∧
    ContinuousCollisionMoments.cubeIntegral R ((u*ContinuousCollisionForm.inverseCube N
      (fun k=>(hm.trans_le (hN k).1).ne'))*
      (fderiv ℝ (collisionMap R hR.le) f (N*u)-fderiv ℝ (collisionMap R hR.le) N (N*u)))=
      (∫q,diagDensity R f N u q∂pairingMeasure R)+(∫q,offDensity R f N u q∂pairingMeasure R) := by
  have ho:=(actual_full_offdiagonal_estimate hR f N u hm hM hκ hf hN hbulk).1
  have hp:=perturbationDensity_integrable hR.le f N u (fun k=>(hm.trans_le (hN k).1).ne')
  have he : perturbationDensity R f N u=diagDensity R f N u+offDensity R f N u := by
    funext q
    exact complete_actual_density_split R f N u q
  have hd:Integrable (diagDensity R f N u) (pairingMeasure R):=by
    apply (hp.sub ho).congr
    apply ae_of_all
    intro q
    simp only [Pi.sub_apply,complete_actual_density_split,add_sub_cancel_right]
  refine ⟨hd,?_⟩
  rw [actual_perturbation_integral hR.le f N u,he]
  exact integral_add hd ho

theorem actual_offdiagonal_cost_tendsto {R : ℝ} (hR : 0<R) (m M : ℝ) :
    Tendsto (fun p:ℝ×ℝ=>energyCost R m M p.1 p.2) (𝓝 (0,0)) (𝓝 0) := by
  have hk : Tendsto (fun p:ℝ×ℝ=>p.1) (𝓝 (0,0)) (𝓝 0):=continuous_fst.continuousAt.tendsto
  have he:=(markedOmega_tendsto hR (unitParameter_positive R)).comp
    (continuous_snd.continuousAt.tendsto (x:=((0,0):ℝ×ℝ)))
  simpa only [energyCost,mul_zero,add_zero] using
    (tendsto_const_nhds.mul hk).add (tendsto_const_nhds.mul he)

end
end Resonance.FullLocalizedDerivativeSplit
