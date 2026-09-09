import Resonance.CrossPairDensity
import Resonance.FiberContinuity

/-! Actual moving-plane geometry for a fixed incoming--outgoing pair.
The Householder chart already used by the exact marginal is retained.
For each output, the excluded input coordinate planes have zero volume. -/
open Real Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Resonance.CrossRowGeometry
noncomputable section
set_option maxHeartbeats 1000000
open Resonance.ResonantMeasure
open Resonance.PlaneCoarea (E2 e0 planePoint householder flatEmbedding)
open Resonance.PlaneGlobal (unitVector direction)
open Resonance.CrossPairCoordinates Resonance.FiberContinuity

theorem unitVector_continuousAt {x:E} (hx:x≠0) : ContinuousAt unitVector x := by
  have he : ∀ᶠy in nhds x,y≠(0:E) := isOpen_ne.mem_nhds hx
  have heq : unitVector =ᶠ[nhds x] (fun y:E=>‖y‖⁻¹ • y) := by
    filter_upwards [he] with y hy
    simp only [unitVector,if_neg hy]
  have hc : ContinuousAt (fun y:E=>‖y‖⁻¹ • y) x :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id
  exact hc.congr_of_eventuallyEq heq

theorem direction_continuousAt {x:E} (hx:x≠0) : ContinuousAt direction x := by
  change Tendsto direction (nhds x) (nhds (direction x))
  rw [tendsto_subtype_rng]
  exact unitVector_continuousAt hx

theorem planePoint_continuousAt {σ:Sphere} (hσ:e0≠(σ:E)) (z:E2) :
    ContinuousAt (fun τ:Sphere=>planePoint τ z) σ := by
  simp only [planePoint,PlaneCoarea.householder_explicit]
  have hc : Continuous (fun τ:Sphere=>e0-(τ:E)) := continuous_const.sub continuous_subtype_val
  have hn : ‖e0-(σ:E)‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hσ))
  exact continuousAt_const.sub
    ((continuousAt_const.mul
      ((hc.continuousAt.inner continuousAt_const).div (hc.norm.pow 2).continuousAt hn)).smul
        hc.continuousAt)

theorem crossQuartet_continuousAt {k p:E} (hpk:p≠k)
    (hσ:e0≠(direction (p-k):E)) (z:E2) :
    ContinuousAt (fun a:E=>crossQuartet ((a,p),z)) k := by
  have hd : ContinuousAt (fun a:E=>direction (p-a)) k :=
    (direction_continuousAt (sub_ne_zero.mpr hpk)).comp
      (continuousAt_const.sub continuousAt_id)
  have hy : ContinuousAt (fun a:E=>planePoint (direction (p-a)) z) k :=
    ContinuousAt.comp (g:=fun τ:Sphere=>planePoint τ z)
      (f:=fun a:E=>direction (p-a)) (planePoint_continuousAt hσ z) hd
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact continuousAt_id
  · exact (continuousAt_id.add (continuousAt_const.sub continuousAt_id)).add hy
  · exact continuousAt_id.add (continuousAt_const.sub continuousAt_id)
  · exact continuousAt_id.add hy

theorem direction_generic_of_coordinates {k p:E} (hp:∀j:Fin 3,p j≠k j) :
    p≠k ∧ ∀j:Fin 3,(direction (p-k):E) j^2≠1 := by
  have hpk:p≠k := fun h=>hp 0 (congrArg (fun x:E=>x 0) h)
  have hx:p-k≠0 := sub_ne_zero.mpr hpk
  have hc (j:Fin 3) : (direction (p-k):E) j≠0 := by
    change unitVector (p-k) j≠0
    simp only [unitVector,if_neg hx,PiLp.smul_apply,smul_eq_mul,PiLp.sub_apply]
    exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx)) (sub_ne_zero.mpr (hp j))
  refine ⟨hpk,?_⟩
  intro j
  have hn:=sphere_norm_coordinates (direction (p-k))
  fin_cases j
  · intro h
    change (direction (p-k):E) 0^2=1 at h
    nlinarith [sq_pos_of_ne_zero (hc 1),sq_nonneg ((direction (p-k):E) 2)]
  · intro h
    change (direction (p-k):E) 1^2=1 at h
    nlinarith [sq_pos_of_ne_zero (hc 0),sq_nonneg ((direction (p-k):E) 2)]
  · intro h
    change (direction (p-k):E) 2^2=1 at h
    nlinarith [sq_pos_of_ne_zero (hc 0),sq_nonneg ((direction (p-k):E) 1)]

theorem input_coordinates_generic_ae (k:E) :
    ∀ᵐp:E∂volume,∀j:Fin 3,p j≠k j := by
  apply Filter.eventually_all.mpr
  intro j
  apply ae_iff.mpr
  simpa only [not_not] using CoareaGlobal.euclidean_coordinate_face_null j (k j)

theorem crossQuartet_one (k p:E) (z:E2) :
    crossQuartet ((k,p),z) 1=p+planePoint (direction (p-k)) z := by
  change k+(p-k)+planePoint (direction (p-k)) z=_
  congr 1
  abel

theorem crossQuartet_three (k p:E) (z:E2) :
    crossQuartet ((k,p),z) 3=k+planePoint (direction (p-k)) z := rfl

theorem cross_leg_level_null {k p:E}
    (hp:∀j:Fin 3,(direction (p-k):E) j^2≠1)
    (i:Fin 4) (hi0:i≠0) (hi2:i≠2) (j:Fin 3) (a:ℝ) :
    (volume:Measure E2) {z|crossQuartet ((k,p),z) i j=a}=0 := by
  fin_cases i
  · exact (hi0 rfl).elim
  · have he : {z:E2|crossQuartet ((k,p),z) 1 j=a}=
        {z:E2|planePoint (direction (p-k)) z j=a-p j} := by
      ext z
      simp only [mem_setOf_eq]
      rw [crossQuartet_one]
      change p j+planePoint (direction (p-k)) z j=a ↔ _
      constructor <;> intro h <;> linarith
    change (volume:Measure E2) {z|crossQuartet ((k,p),z) 1 j=a}=0
    rw [he]
    exact plane_coordinate_level_null _ j (hp j) _
  · exact (hi2 rfl).elim
  · have he : {z:E2|crossQuartet ((k,p),z) 3 j=a}=
        {z:E2|planePoint (direction (p-k)) z j=a-k j} := by
      ext z
      simp only [mem_setOf_eq]
      rw [crossQuartet_three]
      change k j+planePoint (direction (p-k)) z j=a ↔ _
      constructor <;> intro h <;> linarith
    change (volume:Measure E2) {z|crossQuartet ((k,p),z) 3 j=a}=0
    rw [he]
    exact plane_coordinate_level_null _ j (hp j) _

theorem cross_nonfixed_faces_avoided {k p:E}
    (hp:∀j:Fin 3,(direction (p-k):E) j^2≠1) (R:ℝ) :
    ∀ᵐz:E2∂volume,∀i:Fin 4,i≠0→i≠2→∀j:Fin 3,|crossQuartet ((k,p),z) i j|≠R := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi0:i=0
  · exact ae_of_all _ (fun _ h=>False.elim (h hi0))
  by_cases hi2:i=2
  · exact ae_of_all _ (fun _ _ h=>False.elim (h hi2))
  apply Filter.Eventually.mono ?_ (fun _ h _ _=>h)
  apply Filter.eventually_all.mpr
  intro j
  apply ae_iff.mpr
  have hsub : {z:E2|¬|crossQuartet ((k,p),z) i j|≠R}⊆
      {z|crossQuartet ((k,p),z) i j=R}∪{z|crossQuartet ((k,p),z) i j= -R} := by
    intro z hz
    have hh:|crossQuartet ((k,p),z) i j|=R := not_not.mp hz
    rcases le_total 0 (crossQuartet ((k,p),z) i j) with hpos|hneg
    · exact Or.inl (by simpa only [abs_of_nonneg hpos] using hh)
    · exact Or.inr (by
        change crossQuartet ((k,p),z) i j= -R
        rw [abs_of_nonpos hneg] at hh
        linarith)
  exact measure_mono_null hsub (measure_union_null
    (cross_leg_level_null hp i hi0 hi2 j R) (cross_leg_level_null hp i hi0 hi2 j (-R)))

end
end Resonance.CrossRowGeometry
