import Resonance.JointMultiplier
import Resonance.PhaseEnergy

/-! The original common time-space-quartet measure. Spatial Haar volume
is exactly the measure used by PhaseEnergy, without probability rescaling.
Every leg pullback retains this same time and space coordinate. -/
open MeasureTheory MeasureTheory.Measure Set
namespace Resonance.SpacetimePairing
noncomputable section
open ResonantMeasure FreeTransport JointMultiplier

abbrev Base := ℝ×SpatialTorus
abbrev Source := Base×E
abbrev Joint := Base×FourMomenta

def baseMeasure (T : ℝ) : Measure Base :=
  (volume.restrict (Icc 0 T)).prod (volume : Measure SpatialTorus)

instance baseMeasure_finite (T : ℝ) : IsFiniteMeasure (baseMeasure T) := by
  unfold baseMeasure
  infer_instance

def sourceMeasure (R T : ℝ) : Measure Source :=
  (baseMeasure T).prod (volume.restrict (cube R))

def jointMeasure (R T : ℝ) : Measure Joint :=
  (baseMeasure T).prod (pairingMeasure R)

theorem jointMeasure_finite {R : ℝ} (hR : 0≤R) (T : ℝ) :
    IsFiniteMeasure (jointMeasure R T) := by
  letI := pairingMeasure_finite hR
  unfold jointMeasure
  infer_instance

def leg (i : Fin 4) (p : Joint) : Source := (p.1,p.2 i)

theorem leg_quasiMeasurePreserving {R : ℝ} (hR : 0≤R) (T : ℝ) (i : Fin 4) :
    QuasiMeasurePreserving (leg i) (jointMeasure R T) (sourceMeasure R T) := by
  letI : SFinite (volume.restrict (cube R) : Measure E) := inferInstance
  letI := pairingMeasure_finite hR
  exact MeasureTheory.QuasiMeasurePreserving.prodMap
    (MeasurePreserving.id (baseMeasure T)).quasiMeasurePreserving
    (JointMultiplier.leg_quasiMeasurePreserving_cube R i)

theorem joint_full_support (R T : ℝ) :
    ∀ᵐp∂jointMeasure R T,fullResonance R p.2 :=
  Measure.quasiMeasurePreserving_snd.ae
    (ae_iff.mpr (pairing_supported_on_fullResonance R))

theorem base_property_on_joint (R T : ℝ) {P : Base→Prop}
    (hP : ∀ᵐz∂baseMeasure T,P z) : ∀ᵐp∂jointMeasure R T,P p.1 :=
  Measure.quasiMeasurePreserving_fst.ae hP

theorem leg_tendstoInMeasure {R : ℝ} (hR : 0≤R) (T : ℝ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] (i : Fin 4)
    {b : ι→Source→ℝ} {c : Source→ℝ}
    (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hconv : TendstoInMeasure (sourceMeasure R T) b l c) :
    TendstoInMeasure (jointMeasure R T) (fun n p=>b n (leg i p)) l (fun p=>c (leg i p)) := by
  letI := jointMeasure_finite hR T
  exact pullback_tendstoInMeasure (leg_quasiMeasurePreserving hR T i) hb hconv

end
end Resonance.SpacetimePairing
