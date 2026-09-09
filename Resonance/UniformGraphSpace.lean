import Resonance.GraphResolventJets
import Resonance.SupFamilyLinear

/-! The common supremum of the actual complete B_s graphs, indexed by
every real s≥1. Its embedding retains both original continuous outputs. -/
open Set
open scoped ENNReal ContDiff
namespace Resonance.UniformGraphSpace
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open ResonantMeasure RegularizedGraphNorm GraphResolventSmooth
open CubeContinuousEssentialNorm CubeLinftyCoordinates
abbrev Index := Ici (1 : ℝ)
abbrev CX (R : ℝ) := C(cube R,ℝ)
abbrev LX (R : ℝ) := LinftyMultiplication.X R
abbrev Sources (R : ℝ) := lp (fun _ : Index => CX R) ∞
abbrev Space {R : ℝ} (hR : 0≤R) := lp (fun s : Index => graphSpace hR s) ∞
abbrev Ambient (R : ℝ) := lp (fun _ : Index => LX R×LX R) ∞

instance spaceComplete {R : ℝ} (hR : 0≤R) : CompleteSpace (Space hR) := by
  exact @lp.completeSpace Index (fun s : Index => graphSpace hR s) ∞
    (fun s => (graphSpace hR s).normedAddCommGroup) inferInstance
    (fun s => graph_complete hR s)

def fiberEmbed {R : ℝ} (hR : 0<R) (s : Index) :
    graphSpace hR.le s→ₗᵢ[ℝ](LX R×LX R) where
  toLinearMap := ((embed R).prodMap (embed R)).toLinearMap.comp
    (graphSpace hR.le s).subtype
  norm_map' q := by
    change max ‖embed R q.val.1‖ ‖embed R q.val.2‖=max ‖q.val.1‖ ‖q.val.2‖
    rw [embed_norm_eq hR,embed_norm_eq hR]

def embedFamily {R : ℝ} (hR : 0<R) : Space hR.le→ₗᵢ[ℝ]Ambient R :=
  SupFamilyLinear.isometry (fiberEmbed hR)

theorem embedFamily_apply {R : ℝ} (hR : 0<R) (q : Space hR.le) (s : Index) :
    embedFamily hR q s=(embed R (q s).val.1,embed R (q s).val.2) := rfl

def shift (s : Index) : UniformShiftSpace.Shift :=
  RegularizedParameterJets.inverseShift s s.property

def ambientFiber (R : ℝ) (A : UniformShiftSpace.Family R×UniformShiftSpace.Family R)
    (s : Index) : CX R→L[ℝ](LX R×LX R) :=
  ((A.1 (shift s)).comp (embed R)).prod ((A.2 (shift s)).comp (embed R))

theorem ambientFiber_bound (R : ℝ)
    (A : UniformShiftSpace.Family R×UniformShiftSpace.Family R) (s : Index) :
    ‖ambientFiber R A s‖≤‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro F
  change max ‖A.1 (shift s) (embed R F)‖ ‖A.2 (shift s) (embed R F)‖≤_
  apply max_le
  · exact ((A.1 (shift s)).le_opNorm _).trans
      (mul_le_mul ((lp.norm_apply_le_norm ENNReal.top_ne_zero A.1 (shift s)).trans
        (norm_fst_le A)) (extendVector_bound R F) (norm_nonneg _) (norm_nonneg A))
  · exact ((A.2 (shift s)).le_opNorm _).trans
      (mul_le_mul ((lp.norm_apply_le_norm ENNReal.top_ne_zero A.2 (shift s)).trans
        (norm_snd_le A)) (extendVector_bound R F) (norm_nonneg _) (norm_nonneg A))

def ambientOperator (R : ℝ)
    (A : UniformShiftSpace.Family R×UniformShiftSpace.Family R) :
    Sources R→L[ℝ]Ambient R :=
  SupFamilyLinear.diagonal (ambientFiber R A) (norm_nonneg A) (ambientFiber_bound R A)

theorem ambientOperator_apply (R : ℝ)
    (A : UniformShiftSpace.Family R×UniformShiftSpace.Family R) (F : Sources R) (s : Index) :
    ambientOperator R A F s=
      (A.1 (shift s) (embed R (F s)),A.2 (shift s) (embed R (F s))) := rfl

theorem ambientOperator_bound (R : ℝ)
    (A : UniformShiftSpace.Family R×UniformShiftSpace.Family R) :
    ‖ambientOperator R A‖≤‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro F
  apply lp.norm_le_of_forall_le (by positivity)
  intro s
  exact ((ambientFiber R A s).le_opNorm (F s)).trans
    (mul_le_mul (ambientFiber_bound R A s) (lp.norm_apply_le_norm ENNReal.top_ne_zero F s)
      (norm_nonneg _) (norm_nonneg A))

def ambientLinear (R : ℝ) :
    (UniformShiftSpace.Family R×UniformShiftSpace.Family R)→ₗ[ℝ](Sources R→L[ℝ]Ambient R) where
  toFun := ambientOperator R
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro F
    apply lp.ext
    funext s
    change ((A.1 (shift s)+B.1 (shift s)) (embed R (F s)),
      (A.2 (shift s)+B.2 (shift s)) (embed R (F s)))=_
    rfl
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro F
    apply lp.ext
    funext s
    rfl

def ambientMap (R : ℝ) :
    (UniformShiftSpace.Family R×UniformShiftSpace.Family R)→L[ℝ](Sources R→L[ℝ]Ambient R) :=
  (ambientLinear R).mkContinuous 1 (fun A => by simpa using ambientOperator_bound R A)

theorem ambientMap_apply (R : ℝ)
    (A : UniformShiftSpace.Family R×UniformShiftSpace.Family R) :
    ambientMap R A=ambientOperator R A := rfl

end
end Resonance.UniformGraphSpace
