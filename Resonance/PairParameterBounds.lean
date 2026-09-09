import Resonance.QuartetParameterBounds

/-! Parameter comparison is pushed through the actual full sharp plane
and sphere densities. All flags and their physical prefactors remain present. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.PairParameterBounds
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure WeightedJointMeasure Thermodynamics JointWeightComparison
open ActualPairKernels

theorem flagged_integral_add_const {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (R : ℝ) {Q : X→FourMomenta} (hQ : Measurable Q) {w : FourMomenta→ℝ≥0∞}
    (hw : Measurable w) (c : ℝ≥0∞) :
    (∫⁻x,(CoareaNormalization.allFourFlags R).indicator (fun q=>w q+c) (Q x)∂μ)=
      (∫⁻x,(CoareaNormalization.allFourFlags R).indicator w (Q x)∂μ)+
      c*(∫⁻x,(CoareaNormalization.allFourFlags R).indicator (fun _=>1) (Q x)∂μ) := by
  have he : (fun x=>(CoareaNormalization.allFourFlags R).indicator (fun q=>w q+c) (Q x))=
      (fun x=>(CoareaNormalization.allFourFlags R).indicator w (Q x)+
        c*(CoareaNormalization.allFourFlags R).indicator (fun _=>1) (Q x)) := by
    funext x
    by_cases hx : Q x∈CoareaNormalization.allFourFlags R
    · simp only [Set.indicator_of_mem hx,mul_one]
    · simp only [Set.indicator_of_notMem hx,mul_zero,add_zero]
  have hwq : Measurable (fun x=>(CoareaNormalization.allFourFlags R).indicator w (Q x)) :=
    (hw.indicator (CoareaNormalization.allFourFlags_measurable R)).comp hQ
  have h1q : Measurable (fun x=>(CoareaNormalization.allFourFlags R).indicator (fun _=>(1 : ℝ≥0∞)) (Q x)) :=
    (measurable_const.indicator (CoareaNormalization.allFourFlags_measurable R)).comp hQ
  rw [he,lintegral_add_left hwq,lintegral_const_mul _ h1q]

theorem incoming_density_order (R : ℝ) {w v : FourMomenta→ℝ≥0∞}
    (hv : Measurable v) (c : ℝ≥0∞)
    (h : ∀q∈CoareaNormalization.allFourFlags R,w q≤v q+c) (p : E×E) :
    IncomingPairDensity.density R w p≤IncomingPairDensity.density R v p+
      c*IncomingPairDensity.density R (fun _=>1) p := by
  have hQ : Measurable (fun σ=>IncomingPairMarginal.incomingQuartet (p,σ)) :=
    IncomingPairMarginal.incomingQuartet_measurable.comp (measurable_const.prodMk measurable_id)
  unfold IncomingPairDensity.density
  calc
    _ ≤ ENNReal.ofReal (‖p.1-p.2‖/8)*∫⁻σ,
        (CoareaNormalization.allFourFlags R).indicator (fun q=>v q+c)
          (IncomingPairMarginal.incomingQuartet (p,σ))∂surface := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro σ
      by_cases hq : IncomingPairMarginal.incomingQuartet (p,σ)∈CoareaNormalization.allFourFlags R
      · simp only [Set.indicator_of_mem hq]
        exact h _ hq
      · simp only [Set.indicator_of_notMem hq,le_refl]
    _ = _ := by rw [flagged_integral_add_const surface R hQ hv c]; ring

theorem cross_density_order (R : ℝ) {w v : FourMomenta→ℝ≥0∞}
    (hv : Measurable v) (c : ℝ≥0∞)
    (h : ∀q∈CoareaNormalization.allFourFlags R,w q≤v q+c) (p : E×E) :
    CrossPairDensity.density R w p≤CrossPairDensity.density R v p+
      c*CrossPairDensity.density R (fun _=>1) p := by
  have hQ : Measurable (fun z : PlaneCoarea.E2=>CrossPairCoordinates.crossQuartet (p,z)) :=
    CrossPairCoordinates.crossQuartet_measurable.comp (measurable_const.prodMk measurable_id)
  unfold CrossPairDensity.density
  calc
    _ ≤ (1/2 : ℝ≥0∞)*ENNReal.ofReal (‖p.2-p.1‖⁻¹)*∫⁻z : PlaneCoarea.E2,
        (CoareaNormalization.allFourFlags R).indicator (fun q=>v q+c)
          (CrossPairCoordinates.crossQuartet (p,z)) := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro z
      by_cases hq : CrossPairCoordinates.crossQuartet (p,z)∈CoareaNormalization.allFourFlags R
      · simp only [Set.indicator_of_mem hq]
        exact h _ hq
      · simp only [Set.indicator_of_notMem hq,le_refl]
    _ = _ := by rw [flagged_integral_add_const volume R hQ hv c]; ring

theorem toReal_abs_sub_bound {a b t : ℝ≥0∞} {c : ℝ} (hc : 0≤c)
    (ha : a≠∞) (hb : b≠∞) (ht : t≠∞)
    (hab : a≤b+ENNReal.ofReal c*t) (hba : b≤a+ENNReal.ofReal c*t) :
    |a.toReal-b.toReal|≤c*t.toReal := by
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hb,ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht⟩) hab
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ha,ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht⟩) hba
  rw [ENNReal.toReal_add hb (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] at h1
  rw [ENNReal.toReal_add ha (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem compact_pair_difference_bound {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ∈K,∀β∈K,∀p : E×E,
      |(IncomingPairDensity.density R (weight θ) p).toReal-
        (IncomingPairDensity.density R (weight β) p).toReal|≤
        C*‖θ-β‖*(IncomingPairDensity.density R (weight unitParameter) p).toReal ∧
      |(CrossPairDensity.density R (weight θ) p).toReal-
        (CrossPairDensity.density R (weight β) p).toReal|≤
        C*‖θ-β‖*(CrossPairDensity.density R (weight unitParameter) p).toReal := by
  obtain ⟨C,hC,hb⟩ := QuartetParameterBounds.compact_quartet_weight_order hR hK hpos
  have hu : weight unitParameter=(fun _=>1) := by
    funext q
    simp only [weight,unit_profile,Finset.prod_const_one,ENNReal.ofReal_one]
  refine ⟨C,hC,?_⟩
  intro θ hθ β hβ p
  have hrev : ∀q∈CoareaNormalization.allFourFlags R,
      weight β q≤weight θ q+ENNReal.ofReal (C*‖θ-β‖) := by
    intro q hq
    simpa only [norm_sub_rev] using hb β hβ θ hθ q hq
  constructor
  · apply toReal_abs_sub_bound (mul_nonneg hC (norm_nonneg _))
      (incoming_density_finite (hpos hθ) p) (incoming_density_finite (hpos hβ) p)
      (incoming_density_finite (unitParameter_positive R) p)
    · rw [hu]
      exact incoming_density_order R (weight_measurable β) _ (hb θ hθ β hβ) p
    · rw [hu]
      exact incoming_density_order R (weight_measurable θ) _ hrev p
  · apply toReal_abs_sub_bound (mul_nonneg hC (norm_nonneg _))
      (cross_density_finite hR (hpos hθ) p) (cross_density_finite hR (hpos hβ) p)
      (cross_density_finite hR (unitParameter_positive R) p)
    · rw [hu]
      exact cross_density_order R (weight_measurable β) _ (hb θ hθ β hβ) p
    · rw [hu]
      exact cross_density_order R (weight_measurable θ) _ hrev p

theorem compact_pair_upper_bound {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃B : ℝ,0≤B ∧ ∀θ∈K,∀p : E×E,
      (IncomingPairDensity.density R (weight θ) p).toReal≤
        B*(IncomingPairDensity.density R (weight unitParameter) p).toReal ∧
      (CrossPairDensity.density R (weight θ) p).toReal≤
        B*(CrossPairDensity.density R (weight unitParameter) p).toReal := by
  obtain ⟨m,M,hm,hM,hb⟩ := compact_profile_bounds hR hK hpos
  have hu : weight unitParameter=(fun _=>1) := by
    funext q
    simp only [weight,unit_profile,Finset.prod_const_one,ENNReal.ofReal_one]
  refine ⟨M^4,by positivity,?_⟩
  intro θ hθ p
  have hw : ∀q∈CoareaNormalization.allFourFlags R,weight θ q≤(0 : ℝ≥0∞)+ENNReal.ofReal (M^4) := by
    intro q hq
    rw [zero_add]
    apply ENNReal.ofReal_le_ofReal
    exact (Finset.prod_le_prod (fun i _=>(profile_pos (hpos hθ) (hq i)).le)
      (fun i _=>(hb θ hθ _ (hq i)).2)).trans_eq (by simp)
  have hi := incoming_density_order R (v:=fun _=>0) measurable_const (ENNReal.ofReal (M^4)) hw p
  have hc := cross_density_order R (v:=fun _=>0) measurable_const (ENNReal.ofReal (M^4)) hw p
  have hz1 : IncomingPairDensity.density R (fun _=>0) p=0 := by
    simp only [IncomingPairDensity.density,Set.indicator_zero,lintegral_zero,mul_zero]
  have hz2 : CrossPairDensity.density R (fun _=>0) p=0 := by
    simp only [CrossPairDensity.density,Set.indicator_zero,lintegral_zero,mul_zero]
  rw [hz1,zero_add,←hu] at hi
  rw [hz2,zero_add,←hu] at hc
  constructor
  · have he := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (incoming_density_finite (unitParameter_positive R) p)) hi
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤M^4)] using he
  · have he := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (cross_density_finite hR (unitParameter_positive R) p)) hc
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤M^4)] using he

end
end Resonance.PairParameterBounds
