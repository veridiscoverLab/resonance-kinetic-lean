import Resonance.CriticalTripleMollifier
import Resonance.CoordinatePermutation

/-! The second critical energy -uV with its complete uV source. Arbitrary
shrinking kernels converge to zero by the same full-source product integral. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CriticalProductPlaneMollifier
noncomputable section
open LinearSurfaceArea CriticalCoordinateFubini
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def reverseCoordinates : A ≃ₗᵢ[ℝ] A :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 2)

def current (ρ : ℝ → ℝ) (B : A → E) (p : A) : E :=
  (p 1*p 2) • (ρ (-(p 1*p 2)) • B p)

def amplitude (B : A → E) (p : P × ℝ) : E :=
  p.2 • B (reverseCoordinates (split.symm p))

omit [CompleteSpace E] in
theorem amplitude_regular {B : A → E} (hc : Continuous B) (hK : HasCompactSupport B) :
    Continuous (amplitude B) ∧ HasCompactSupport (amplitude B) := by
  have hC := (hc.comp reverseCoordinates.continuous).comp split_symm_continuous
  have hKs := split_compact_support (CoordinatePermutation.compact_pullback reverseCoordinates hK)
  exact ⟨continuous_snd.smul hC,hKs.smul_left⟩

omit [CompleteSpace E] in
theorem current_split (ρ : ℝ → ℝ) (B : A → E) (p : P × ℝ) :
    current ρ B (reverseCoordinates (split.symm p))=
      p.1 0 • (ρ (-p.1 0*p.2) • amplitude B p) := by
  have h1 : reverseCoordinates (split.symm p) 1=p.1 0 := by
    rw [split_symm_apply]
    rfl
  have h2 : reverseCoordinates (split.symm p) 2=p.2 := by
    rw [split_symm_apply]
    rfl
  simp only [current,h1,h2,amplitude,neg_mul]
  simp only [smul_smul]
  congr 1
  ring

omit [CompleteSpace E] in
theorem current_integrable {B : A → E} (hc : Continuous B) (hK : HasCompactSupport B)
    {ρ : ℝ → ℝ} (hm : Measurable ρ) (hρ : Integrable ρ)
    (hpos : ∀q,0≤ρ q) (hmass : ∫q,ρ q=1) : Integrable (current ρ B) := by
  have hA := amplitude_regular hc hK
  have hi := CompactCriticalProduct.complete_integrable (volume : Measure P) hA.1 hA.2 hm hρ hpos hmass
    (fun x : P=>x 0) (PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 0).measurable
  have he : (current ρ B ∘ reverseCoordinates ∘ split.symm)=
      fun p : P × ℝ=>p.1 0 • (ρ (-p.1 0*p.2) • amplitude B p) := funext (current_split ρ B)
  rw [←he] at hi
  have hi1 : Integrable (fun p=>current ρ B (reverseCoordinates p)) :=
    (split_volume_preserving.symm.integrable_comp_emb split.symm.measurableEmbedding).mp hi
  exact (reverseCoordinates.measurePreserving.integrable_comp_emb
    reverseCoordinates.toMeasurableEquiv.measurableEmbedding).mp hi1

theorem current_tendsto {B : A → E} (hc : Continuous B) (hK : HasCompactSupport B)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    Tendsto (fun η=>∫p,current (ρ η) B p) (𝓝[>]0) (𝓝 0) := by
  have hA := amplitude_regular hc hK
  have ht := CompactCriticalProduct.complete_tendsto (volume : Measure P) hA.1 hA.2
    (fun x : P=>x 0) (PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 0).measurable
    ρ hm hρ hpos hmass hs
  simp only [amplitude,zero_smul,smul_zero,integral_zero] at ht
  apply ht.congr
  intro η
  rw [←reverseCoordinates.measurePreserving.integral_comp
    reverseCoordinates.toMeasurableEquiv.measurableEmbedding (current (ρ η) B)]
  rw [←split_volume_preserving.symm.integral_comp split.symm.measurableEmbedding
    (fun p=>current (ρ η) B (reverseCoordinates p))]
  exact integral_congr_ae (ae_of_all _ (fun p=>(current_split (ρ η) B p).symm))

end
end Resonance.CriticalProductPlaneMollifier
