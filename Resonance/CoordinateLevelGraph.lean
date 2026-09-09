import Resonance.ControlledCoordinateChart
import Resonance.RegularGraphCoarea

/-! Every level in a genuine scalar coordinate chart is the actual full graph
of its inverse, including the entire source-level intersection. -/
open Set
open scoped ContDiff Topology ENNReal
namespace Resonance.CoordinateLevelGraph
noncomputable section
open PinnedMeasure CoordinateReplacement ControlledCoordinateChart
open LinearSurfaceArea C1GraphArea

def levelEmbedding (s : ℝ) (x : P) : A := WithLp.toLp 2 ![x 0,s,x 1]
def levelDomain (e : OpenPartialHomeomorph A A) (s : ℝ) : Set P :=
  levelEmbedding s ⁻¹' e.target
def levelHeight (e : OpenPartialHomeomorph A A) (s : ℝ) (x : P) : ℝ :=
  e.symm (levelEmbedding s x) 1

theorem levelEmbedding_contDiff (s : ℝ) : ContDiff ℝ 1 (levelEmbedding s) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> dsimp [levelEmbedding] <;> fun_prop

theorem levelDomain_open (e : OpenPartialHomeomorph A A) (s : ℝ) : IsOpen (levelDomain e s) :=
  e.open_target.preimage (levelEmbedding_contDiff s).continuous

theorem levelHeight_contDiffOn (e : OpenPartialHomeomorph A A)
    (he : ContDiffOn ℝ 1 e.symm e.target) (s : ℝ) :
    ContDiffOn ℝ 1 (levelHeight e s) (levelDomain e s) := by
  have h := he.comp (levelEmbedding_contDiff s).contDiffOn (fun _ hx => hx)
  exact (coordinateProjection 1).contDiff.comp_contDiffOn h

theorem level_graph_eq_inverse {F : A → ℝ} (e : OpenPartialHomeomorph A A)
    (he : (e : A → A)=replace 1 F) (s : ℝ) {x : P} (hx : x∈levelDomain e s) :
    graph (levelHeight e s) x=e.symm (levelEmbedding s x) := by
  have hi := coordinate_level_inverse e he hx
  ext i
  fin_cases i
  · exact hi.2.1.symm
  · rfl
  · exact hi.2.2.symm

theorem level_graph_energy {F : A → ℝ} (e : OpenPartialHomeomorph A A)
    (he : (e : A → A)=replace 1 F) (s : ℝ) {x : P} (hx : x∈levelDomain e s) :
    F (graph (levelHeight e s) x)=s := by
  rw [level_graph_eq_inverse e he s hx]
  exact (coordinate_level_inverse e he hx).1

theorem source_level_eq_image {F : A → ℝ} (e : OpenPartialHomeomorph A A)
    (he : (e : A → A)=replace 1 F) (s : ℝ) :
    e.source ∩ {p | F p=s}=graph (levelHeight e s) '' levelDomain e s := by
  ext p
  constructor
  · rintro ⟨hpS,hpF⟩
    change F p=s at hpF
    let x : P := WithLp.toLp 2 ![p 0,p 2]
    have hq : levelEmbedding s x=e p := by
      rw [he]
      ext i
      fin_cases i <;> simp [levelEmbedding,x,replace_apply,hpF,
        show (2:Fin 3)≠1 by decide]
    have hx : x∈levelDomain e s := by
      change levelEmbedding s x∈e.target
      rw [hq]
      exact e.map_source hpS
    refine ⟨x,hx,?_⟩
    rw [level_graph_eq_inverse e he s hx,hq,e.left_inv hpS]
  · rintro ⟨x,hx,rfl⟩
    refine ⟨?_,level_graph_energy e he s hx⟩
    rw [level_graph_eq_inverse e he s hx]
    exact e.map_target hx

end
end Resonance.CoordinateLevelGraph
