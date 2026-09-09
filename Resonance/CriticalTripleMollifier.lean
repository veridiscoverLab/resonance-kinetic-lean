import Resonance.CriticalCoordinateFubini
import Resonance.CompactCriticalProduct

/-! The actual Euclidean three-variable integral at energy -quv. Its full
linear source uv is kept inside the integral, including both coordinate axes. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CriticalTripleMollifier
noncomputable section
open LinearSurfaceArea CriticalCoordinateFubini
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def current (ρ : ℝ → ℝ) (B : A → E) (p : A) : E :=
  (p 1*p 2) • (ρ (-(p 1*p 2)*p 0) • B p)

def reading (B : A → E) : E := ∫x : P,(x 0*x 1/|x 0*x 1|) • B (CriticalCoordinateFubini.join x 0)

omit [CompleteSpace E] in
theorem current_split (ρ : ℝ → ℝ) (B : A → E) (p : P × ℝ) :
    current ρ B (split.symm p)=(p.1 0*p.1 1) •
      (ρ (-(p.1 0*p.1 1)*p.2) • (B ∘ split.symm) p) := by
  simp only [current,split_symm_apply,CriticalCoordinateFubini.join,Function.comp_apply]
  rfl

omit [CompleteSpace E] in
theorem current_integrable {B : A → E} (hB : Continuous B) (hK : HasCompactSupport B)
    {ρ : ℝ → ℝ} (hm : Measurable ρ) (hρ : Integrable ρ)
    (hpos : ∀q,0≤ρ q) (hmass : ∫q,ρ q=1) : Integrable (current ρ B) := by
  have hc := hB.comp split_symm_continuous
  have hk := split_compact_support hK
  have hi := CompactCriticalProduct.complete_integrable (volume : Measure P) hc hk hm hρ hpos hmass
    (fun x : P=>x 0*x 1) ((PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 0).mul
      (PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 1)).measurable
  have he : (current ρ B ∘ split.symm)=fun p : P × ℝ=>(p.1 0*p.1 1) •
      (ρ (-(p.1 0*p.1 1)*p.2) • (B ∘ split.symm) p) := funext (current_split ρ B)
  rw [←he] at hi
  exact (split_volume_preserving.symm.integrable_comp_emb split.symm.measurableEmbedding).mp hi

theorem current_tendsto {B : A → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    Tendsto (fun η=>∫p,current (ρ η) B p) (𝓝[>]0) (𝓝 (reading B)) := by
  have ht := CompactCriticalProduct.complete_tendsto (volume : Measure P)
    (hB.comp split_symm_continuous) (split_compact_support hK)
    (fun x : P=>x 0*x 1) ((PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 0).mul
      (PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 1)).measurable
    ρ hm hρ hpos hmass hs
  have he0 : (∫x : P,(x 0*x 1/|x 0*x 1|) • (B ∘ split.symm) (x,0))=reading B := by
    simp only [reading,Function.comp_apply,split_symm_apply]
  rw [he0] at ht
  apply ht.congr
  intro η
  rw [←split_volume_preserving.symm.integral_comp split.symm.measurableEmbedding (current (ρ η) B)]
  exact integral_congr_ae (ae_of_all _ (fun p=>(current_split (ρ η) B p).symm))

end
end Resonance.CriticalTripleMollifier
