import Resonance.CornerRoleGeometry

/-! Simultaneous reflection transports actual corner events of all
four legs and the output, including mixed signs. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.SignedCornerEvents
noncomputable section
open ResonantMeasure CollisionFiber CollisionFrequency CubeFrequencyReflection
open CornerLayerVolume OppositeCornerBox CornerRoleGeometry FixedOutputMeasureSymmetry
set_option maxHeartbeats 1200000

def signedCorner (R ρ : ℝ) (k : E) : Set E :=
  {p | reflectionAt k p∈upperCorner R ρ}

def wrongSignedLayer (R ρ : ℝ) (k : E) (l : Fin 4) : Set FourMomenta :=
  {q | q l∈coordinateLayer R ρ ∧ q l∉signedCorner R ρ k}

theorem reflected_layer_iff (R ρ : ℝ) (k p : E) :
    reflectionAt k p∈coordinateLayer R ρ ↔ p∈coordinateLayer R ρ := by
  change (∀i,|reflectionAt k p i| ≤ R ∧ R-ρ ≤ |reflectionAt k p i|) ↔
    (∀i,|p i| ≤ R ∧ R-ρ ≤ |p i|)
  simp_rw [reflectionAt_abs]

theorem wrongSignedLayer_measurable (R ρ : ℝ) (k : E) (l : Fin 4) :
    MeasurableSet (wrongSignedLayer R ρ k l) :=
  (legLayer_measurable R ρ l).inter
    ((upperCorner_measurable R ρ).preimage
      ((reflectionAt k).continuous.measurable.comp (by fun_prop))).compl

theorem original_layer_reflection {R : ℝ} (hR : 0 ≤ R) (ρ : ℝ) (k : E)
    (hk : k∈cube R) (l : Fin 4) :
    fiberMeasure R k (legLayer R ρ l)=fiberMeasure R (reflectionAt k k) (legLayer R ρ l) := by
  have h := congrArg (fun μ : Measure FourMomenta => μ (legLayer R ρ l))
    (original_fiber_isometry hR (reflectionAt k) (reflectionAt_cube R k) k hk)
  dsimp only at h
  have hT : Measurable (fun q : FourMomenta => fun j => reflectionAt k (q j)) :=
    (continuous_pi (fun j => (reflectionAt k).continuous.comp (continuous_apply j))).measurable
  rw [Measure.map_apply hT (legLayer_measurable R ρ l)] at h
  have hs : (fun q : FourMomenta => fun j => reflectionAt k (q j)) ⁻¹' legLayer R ρ l=
      legLayer R ρ l := by
    ext q
    exact reflected_layer_iff R ρ k (q l)
  rwa [hs] at h

theorem original_wrong_reflection {R : ℝ} (hR : 0 ≤ R) (ρ : ℝ) (k : E)
    (hk : k∈cube R) (l : Fin 4) :
    fiberMeasure R k (wrongSignedLayer R ρ k l)=
      fiberMeasure R (reflectionAt k k) (wrongUpperLayer R ρ l) := by
  have h := congrArg (fun μ : Measure FourMomenta => μ (wrongUpperLayer R ρ l))
    (original_fiber_isometry hR (reflectionAt k) (reflectionAt_cube R k) k hk)
  dsimp only at h
  have hT : Measurable (fun q : FourMomenta => fun j => reflectionAt k (q j)) :=
    (continuous_pi (fun j => (reflectionAt k).continuous.comp (continuous_apply j))).measurable
  rw [Measure.map_apply hT (wrongUpperLayer_measurable R ρ l)] at h
  have hs : (fun q : FourMomenta => fun j => reflectionAt k (q j)) ⁻¹' wrongUpperLayer R ρ l=
      wrongSignedLayer R ρ k l := by
    ext q
    change (reflectionAt k (q l)∈coordinateLayer R ρ ∧
      reflectionAt k (q l)∉upperCorner R ρ) ↔
      (q l∈coordinateLayer R ρ ∧ reflectionAt k (q l)∉upperCorner R ρ)
    rw [reflected_layer_iff]
  rwa [hs] at h

theorem original_frequency_reflection {R : ℝ} (hR : 0 ≤ R) (k : E) (hk : k∈cube R) :
    geometricFrequency R (reflectionAt k k)=geometricFrequency R k := by
  have h := congrArg ENNReal.toReal
    (geometricFrequency_isometry hR (reflectionAt k) (reflectionAt_cube R k) k hk)
  simpa only [ENNReal.toReal_ofReal (geometricFrequency_nonnegative _ _)] using h

end
end Resonance.SignedCornerEvents
