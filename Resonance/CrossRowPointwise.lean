import Resonance.CrossRowGeometry

/-! Pointwise continuity of the original full sharp plane marginal,
within the original output cube and outside a proved null set of input
momenta.  Neither moving-face continuity nor fiber integrability is
assumed. -/
open Real Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Resonance.CrossRowPointwise
noncomputable section
set_option maxHeartbeats 1000000
open Resonance.ResonantMeasure
open Resonance.PlaneCoarea (E2 e0)
open Resonance.CrossPairCoordinates Resonance.CrossRowGeometry
open Resonance.FiberContinuity

def planeIntegral (R:ℝ) (Φ:FourMomenta→ℝ) (k p:E) : ℝ :=
  ∫z:E2,CoareaNormalization.sharpReadout R Φ (crossQuartet ((k,p),z))

def planeRow (R:ℝ) (Φ:FourMomenta→ℝ) (k p:E) : ℝ :=
  (2*‖p-k‖)⁻¹*planeIntegral R Φ k p

def finitePlaneMeasure (R:ℝ) : Measure E2 :=
  volume.restrict (closedBall (0:E2) (6*R))

instance (R:ℝ) : IsFiniteMeasure (finitePlaneMeasure R) :=
  ⟨by rw [finitePlaneMeasure,Measure.restrict_apply_univ];
      exact (isCompact_closedBall (0:E2) (6*R)).measure_lt_top⟩

theorem crossQuartet_source_bound {R:ℝ} (hR:0≤R) (k p:E) {z:E2}
    (hz:crossQuartet ((k,p),z)∈CoareaNormalization.allFourFlags R) :
    z∈closedBall (0:E2) (6*R) := by
  have hbound := PlaneGlobal.rectangle_flags_bounds hR k (p-k)
    (PlaneCoarea.planePoint (PlaneGlobal.direction (p-k)) z) hz
  have hn:‖z‖≤6*R := by
    simpa only [PlaneCoarea.planePoint_eq,LinearIsometry.norm_map] using hbound.2.2
  simpa only [mem_closedBall,dist_zero_right] using hn

theorem planeIntegral_box {R:ℝ} (hR:0≤R) (Φ:FourMomenta→ℝ) (k p:E) :
    planeIntegral R Φ k p=
      ∫z:E2,CoareaNormalization.sharpReadout R Φ (crossQuartet ((k,p),z)) ∂finitePlaneMeasure R := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact Set.indicator_of_notMem (fun h=>hz (crossQuartet_source_bound hR k p h)) Φ

theorem crossSharp_bound {R B:ℝ} (hB:0≤B) (Φ:FourMomenta→ℝ)
    (hΦ:∀q∈CoareaNormalization.allFourFlags R,‖Φ q‖≤B) (k p:E) (z:E2) :
    ‖CoareaNormalization.sharpReadout R Φ (crossQuartet ((k,p),z))‖≤B := by
  by_cases hq:crossQuartet ((k,p),z)∈CoareaNormalization.allFourFlags R
  · rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem hq]
    exact hΦ _ hq
  · rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem hq,norm_zero]
    exact hB

theorem crossSharp_continuousWithinAt (R:ℝ) (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ)
    {k p:E} (hk:k∈cube R) (hpk:p≠k)
    (hσ:e0≠(PlaneGlobal.direction (p-k):E)) (z:E2)
    (hz:∀i:Fin 4,i≠0→i≠2→∀j:Fin 3,|crossQuartet ((k,p),z) i j|≠R) :
    ContinuousWithinAt (fun a:E=>CoareaNormalization.sharpReadout R Φ
      (crossQuartet ((a,p),z))) (cube R) k := by
  have hc:=crossQuartet_continuousAt hpk hσ z
  have hcoords : ∀ᶠa in nhds k,∀i:Fin 4,i≠0→i≠2→∀j:Fin 3,
      (|crossQuartet ((a,p),z) i j|≤R ↔ |crossQuartet ((k,p),z) i j|≤R) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi0:i=0
    · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h hi0))
    by_cases hi2:i=2
    · exact Filter.Eventually.of_forall (fun _ _ h=>False.elim (h hi2))
    apply Filter.Eventually.mono ?_ (fun _ h _ _=>h)
    apply Filter.eventually_all.mpr
    intro j
    have hout:Continuous (fun q:FourMomenta=>|q i j|) := by fun_prop
    exact coordinate_threshold_eventually (hout.continuousAt.comp hc) (hz i hi0 hi2 j)
  have hflags : ∀ᶠa in nhdsWithin k (cube R),
      (crossQuartet ((a,p),z)∈CoareaNormalization.allFourFlags R ↔
        crossQuartet ((k,p),z)∈CoareaNormalization.allFourFlags R) := by
    filter_upwards [hcoords.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with a ha hacube
    change (∀i,∀j,|crossQuartet ((a,p),z) i j|≤R) ↔ (∀i,∀j,|crossQuartet ((k,p),z) i j|≤R)
    apply forall_congr'
    intro i
    by_cases hi0:i=0
    · subst i
      simpa only [crossQuartet_first] using (iff_of_true hacube hk)
    by_cases hi2:i=2
    · subst i
      simp only [crossQuartet_third]
    · exact forall_congr' (fun j=>ha i hi0 hi2 j)
  by_cases h0:crossQuartet ((k,p),z)∈CoareaNormalization.allFourFlags R
  · have heq : (fun a:E=>CoareaNormalization.sharpReadout R Φ (crossQuartet ((a,p),z)))
        =ᶠ[nhdsWithin k (cube R)] (fun a=>Φ (crossQuartet ((a,p),z))) := by
      filter_upwards [hflags] with a ha
      exact Set.indicator_of_mem (ha.mpr h0) Φ
    change Tendsto _ _ (nhds (CoareaNormalization.sharpReadout R Φ (crossQuartet ((k,p),z))))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem h0]
    exact (hΦ.continuousAt.comp hc).continuousWithinAt.tendsto.congr' heq.symm
  · have heq : (fun a:E=>CoareaNormalization.sharpReadout R Φ (crossQuartet ((a,p),z)))
        =ᶠ[nhdsWithin k (cube R)] (fun _=>(0:ℝ)) := by
      filter_upwards [hflags] with a ha
      exact Set.indicator_of_notMem (fun h=>h0 (ha.mp h)) Φ
    change Tendsto _ _ (nhds (CoareaNormalization.sharpReadout R Φ (crossQuartet ((k,p),z))))
    rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem h0]
    exact tendsto_const_nhds.congr' heq.symm

theorem planeIntegral_continuousWithinAt {R:ℝ} (hR:0≤R)
    (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ) {k p:E} (hk:k∈cube R)
    (hp:∀j:Fin 3,p j≠k j) :
    ContinuousWithinAt (fun a:E=>planeIntegral R Φ a p) (cube R) k := by
  obtain ⟨hpk,hgeneric⟩:=direction_generic_of_coordinates hp
  have hσ:e0≠(PlaneGlobal.direction (p-k):E) := by
    intro h
    apply hgeneric 0
    rw [←h]
    norm_num [PlaneCoarea.e0]
  obtain ⟨B,hB,hbound⟩:=PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  simp_rw [planeIntegral_box hR]
  change Tendsto _ (nhdsWithin k (cube R)) _
  apply tendsto_integral_filter_of_dominated_convergence (fun _:E2=>B)
  · exact Filter.Eventually.of_forall (fun a=>
      ((CoareaNormalization.sharpReadout_measurable R hΦ.measurable).comp
        (crossQuartet_measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun a=>ae_of_all _ (crossSharp_bound hB Φ hbound a p))
  · exact integrable_const B
  · have ha:=ae_restrict_of_ae (s:=closedBall (0:E2) (6*R)) (cross_nonfixed_faces_avoided hgeneric R)
    filter_upwards [ha] with z hz
    exact (crossSharp_continuousWithinAt R Φ hΦ hk hpk hσ z hz).tendsto

theorem planeRow_continuousWithinAt {R:ℝ} (hR:0≤R)
    (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ) {k p:E} (hk:k∈cube R)
    (hp:∀j:Fin 3,p j≠k j) :
    ContinuousWithinAt (fun a:E=>planeRow R Φ a p) (cube R) k := by
  have hpk:p≠k := (direction_generic_of_coordinates hp).1
  have hd:ContinuousAt (fun a:E=>(2*‖p-a‖)⁻¹) k :=
    (continuousAt_const.mul (continuousAt_const.sub continuousAt_id).norm).inv₀
      (mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpk)))
  exact hd.continuousWithinAt.mul (planeIntegral_continuousWithinAt hR Φ hΦ hk hp)

theorem planeRow_continuousWithinAt_ae {R:ℝ} (hR:0≤R)
    (Φ:FourMomenta→ℝ) (hΦ:Continuous Φ) {k:E} (hk:k∈cube R) :
    ∀ᵐp:E∂volume,ContinuousWithinAt (fun a:E=>planeRow R Φ a p) (cube R) k := by
  filter_upwards [input_coordinates_generic_ae k] with p hp
  exact planeRow_continuousWithinAt hR Φ hΦ hk hp

end
end Resonance.CrossRowPointwise
