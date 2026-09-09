import Resonance.CornerConvolution
import Resonance.FixedEnergyCoarea
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Exact six-dimensional coordinate rearrangement for the sharp cube.
The three polygon inputs are the three physical coordinate pairs. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CubeAxisCoordinates
noncomputable section
set_option maxHeartbeats 800000
open Resonance.ResonantMeasure (cube)
open Resonance.PlaneCoarea
open Resonance.CornerProductCoordinates Resonance.AxisProductDensity
open Resonance.CornerConvolution

abbrev AxisPair := ℝ×ℝ
abbrev TriplePair := AxisPair×(AxisPair×AxisPair)

def tripleToPi : TriplePair≃ᵐ(Fin 3→AxisPair) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl AxisPair)
    (MeasurableEquiv.piFinTwo (fun _:Fin 2=>AxisPair)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _:Fin 3=>AxisPair) 0).symm

theorem tripleToPi_preserving : MeasurePreserving tripleToPi volume volume := by
  exact ((MeasurePreserving.id (volume:Measure AxisPair)).prod
    (volume_preserving_piFinTwo (fun _:Fin 2=>AxisPair)).symm).trans
    (volume_preserving_piFinSuccAbove (fun _:Fin 3=>AxisPair) 0).symm

@[simp] theorem tripleToPi_zero (p:TriplePair) : tripleToPi p 0=p.1 := rfl
@[simp] theorem tripleToPi_one (p:TriplePair) : tripleToPi p 1=p.2.1 := rfl
@[simp] theorem tripleToPi_two (p:TriplePair) : tripleToPi p 2=p.2.2 := rfl

def axesToPair (p:Fin 3→AxisPair) : E×E :=
  (WithLp.toLp 2 (fun i=>(p i).1),WithLp.toLp 2 (fun i=>(p i).2))

theorem axesToPair_preserving : MeasurePreserving axesToPair volume volume := by
  exact ((PiLp.volume_preserving_toLp (Fin 3)).prod
    (PiLp.volume_preserving_toLp (Fin 3))).comp
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3))

def tripleToPair (p:TriplePair) : E×E := axesToPair (tripleToPi p)

theorem tripleToPair_preserving : MeasurePreserving tripleToPair volume volume :=
  axesToPair_preserving.comp tripleToPi_preserving

@[simp] theorem tripleToPair_fst (p:TriplePair) (i:Fin 3) :
    (tripleToPair p).1 i=(tripleToPi p i).1 := rfl
@[simp] theorem tripleToPair_snd (p:TriplePair) (i:Fin 3) :
    (tripleToPair p).2 i=(tripleToPi p i).2 := rfl

theorem tripleToPair_inner (p:TriplePair) :
    inner ℝ (tripleToPair p).1 (tripleToPair p).2=
      p.1.1*p.1.2+p.2.1.1*p.2.1.2+p.2.2.1*p.2.2.2 := by
  rw [PiLp.inner_apply,Fin.sum_univ_three]
  change p.1.2*p.1.1+p.2.1.2*p.2.1.1+p.2.2.2*p.2.2.1=_
  ring

def normalizedOutput (d:Fin 3→ℝ) : E := WithLp.toLp 2 (fun i=>1/2-d i)

theorem normalizedOutput_mem {d:Fin 3→ℝ} (hd0:∀i,0≤d i) (hd1:∀i,d i≤1) :
    normalizedOutput d∈cube (1/2) := by
  intro i
  change |1/2-d i|≤(1/2:ℝ)
  rw [abs_le]
  constructor <;> linarith [hd0 i,hd1 i]

theorem normalized_coordinate_flags (d x y:ℝ) :
    (|1/2-d+x|≤(1/2:ℝ) ∧ |1/2-d+y|≤(1/2:ℝ) ∧
      |1/2-d+x+y|≤(1/2:ℝ)) ↔ (x,y)∈axisDomain d := by
  simp only [axisDomain,mem_setOf_eq,mem_Icc,abs_le]
  constructor
  · rintro ⟨hx,hy,hxy⟩
    exact ⟨⟨by linarith[hx.1],by linarith[hx.2]⟩,
      ⟨by linarith[hy.1],by linarith[hy.2]⟩,
      ⟨by linarith[hxy.1],by linarith[hxy.2]⟩⟩
  · rintro ⟨hx,hy,hxy⟩
    exact ⟨⟨by linarith[hx.1],by linarith[hx.2]⟩,
      ⟨by linarith[hy.1],by linarith[hy.2]⟩,
      ⟨by linarith[hxy.1],by linarith[hxy.2]⟩⟩

theorem normalized_full_flags {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i≤1) (p:TriplePair) :
    (∀l:Fin 4,rectangleFour (normalizedOutput d) (tripleToPair p).1
      (tripleToPair p).2 l∈cube (1/2)) ↔
      (p.1∈axisDomain (d 0) ∧ p.2.1∈axisDomain (d 1) ∧
        p.2.2∈axisDomain (d 2)) := by
  have hpoint : (∀i:Fin 3,tripleToPi p i∈axisDomain (d i)) ↔
      (p.1∈axisDomain (d 0) ∧ p.2.1∈axisDomain (d 1) ∧
        p.2.2∈axisDomain (d 2)) := by
    simp [Fin.forall_fin_succ]
  rw [←hpoint]
  constructor
  · intro h i
    apply (normalized_coordinate_flags (d i) ((tripleToPair p).1 i)
      ((tripleToPair p).2 i)).mp
    refine ⟨h 2 i,h 3 i,?_⟩
    change |1/2-d i+(tripleToPair p).1 i+(tripleToPair p).2 i|≤(1/2:ℝ)
    exact h 1 i
  · intro h l i
    have hp := (normalized_coordinate_flags (d i) ((tripleToPair p).1 i)
      ((tripleToPair p).2 i)).mpr (h i)
    fin_cases l
    · exact normalizedOutput_mem hd0 hd1 i
    · exact hp.2.2
    · exact hp.1
    · exact hp.2.1

theorem polygonSource_full_integral (d:Fin 3→ℝ) (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    polygonSource d F=
      ∫⁻p:TriplePair,(axisDomain (d 0)×ˢ(axisDomain (d 1)×ˢaxisDomain (d 2))).indicator
        (fun p=>F (p.1.1*p.1.2+p.2.1.1*p.2.1.2+p.2.2.1*p.2.2.2)) p := by
  have hs : MeasurableSet (axisDomain (d 0)×ˢ(axisDomain (d 1)×ˢaxisDomain (d 2))) :=
    (axisDomain_measurable _).prod ((axisDomain_measurable _).prod (axisDomain_measurable _))
  rw [lintegral_indicator hs]
  change polygonSource d F=∫⁻p:TriplePair,
    F (p.1.1*p.1.2+p.2.1.1*p.2.1.2+p.2.2.1*p.2.2.2)
    ∂(((volume:Measure AxisPair).prod ((volume:Measure AxisPair).prod volume)).restrict
      (axisDomain (d 0)×ˢ(axisDomain (d 1)×ˢaxisDomain (d 2))))
  rw [←Measure.prod_restrict,←Measure.prod_restrict]
  have h : Measurable (fun p:TriplePair=>
      F (p.1.1*p.1.2+p.2.1.1*p.2.1.2+p.2.2.1*p.2.2.2)) := hF.comp (by fun_prop)
  rw [lintegral_prod _ h.aemeasurable]
  apply lintegral_congr
  intro p₀
  have hi : Measurable (fun p:AxisPair×AxisPair=>
      F (p₀.1*p₀.2+p.1.1*p.1.2+p.2.1*p.2.2)) := hF.comp (by fun_prop)
  rw [lintegral_prod _ hi.aemeasurable]
  rfl

/-- The literal physical six-dimensional sharp integral, at normalized
radius one half, equals the complete three-polygon sum law. -/
theorem normalized_sharp_lintegral {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i<1) (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻p:E×E,{p:E×E | ∀l:Fin 4,rectangleFour (normalizedOutput d) p.1 p.2 l∈cube (1/2)}.indicator
      (fun p=>F (inner ℝ p.1 p.2)) p)=
      ∫⁻E:ℝ,F E*sumDensity d E := by
  classical
  rw [←polygon_sum_density d hd0 hd1 F hF,polygonSource_full_integral d F hF]
  let G : E×E→ℝ≥0∞ := {p:E×E | ∀l:Fin 4,
    rectangleFour (normalizedOutput d) p.1 p.2 l∈cube (1/2)}.indicator
    (fun p=>F (inner ℝ p.1 p.2))
  have hflags : MeasurableSet {p:E×E | ∀l:Fin 4,
      rectangleFour (normalizedOutput d) p.1 p.2 l∈cube (1/2)} := by
    exact (CoareaNormalization.allFourFlags_measurable (1/2)).preimage
      (rectangleFour_continuous.measurable.comp
        (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  have hG : Measurable G := (hF.comp (by fun_prop)).indicator hflags
  have he := lintegral_map (μ:=(volume:Measure TriplePair)) hG tripleToPair_preserving.measurable
  rw [tripleToPair_preserving.map_eq] at he
  change (∫⁻p:E×E,G p)=_
  rw [he]
  apply lintegral_congr
  intro p
  dsimp only [G]
  simp only [Set.indicator_apply,mem_setOf_eq,mem_prod]
  simp only [normalized_full_flags hd0 (fun i=>(hd1 i).le),tripleToPair_inner]

end
end Resonance.CubeAxisCoordinates
