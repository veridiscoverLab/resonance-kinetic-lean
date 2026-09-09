import Resonance.SignedFiberReadout

/-! Original cubic parents with one frequency-weighted input. Pair
readouts are identified with the same full collision fiber before norms
are transferred back to continuous functions on the closed cube. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.OneWeightedParent
noncomputable section
set_option maxHeartbeats 2200000
open ResonantMeasure ActualPairNormalization CubeLinftyCoordinates
open CollisionMultilinear OneWeightedPairReadout QuartetWeightSpace SignedFiberReadout

def parent (R : ℝ) (hR : 0≤R) (l i j : Fin 4) (u g h : C(cube R,ℝ)) : C(cube R,ℝ) :=
  parentContinuous R hR ![l,i,j] ![u,g,h]

def parentTest (R : ℝ) (l i j : Fin 4) (u g h : C(cube R,ℝ)) : FourMomenta→ℝ :=
  fun q=>pointParent R ![l,i,j] q ![u,g,h]

theorem parentTest_measurable (R : ℝ) (l i j : Fin 4) (u g h : C(cube R,ℝ)) :
    Measurable (parentTest R l i j u g h) := pointParent_measurable R _ _

theorem parentTest_bound (R : ℝ) (l i j : Fin 4) (u g h : C(cube R,ℝ)) (q : FourMomenta) :
    ‖parentTest R l i j u g h q‖≤‖u‖*‖g‖*‖h‖ := by
  simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,Matrix.cons_val_zero,
    Matrix.cons_val_succ,mul_assoc] using pointParent_bound R ![l,i,j] q ![u,g,h]

theorem zeroExtension_outside (R : ℝ) (u : C(cube R,ℝ)) {p : E} (hp : p∉cube R) :
    zeroExtension R u p=0 := by
  unfold zeroExtension
  apply Function.extend_apply'
  rintro ⟨a,ha⟩
  exact hp (ha ▸ a.property)

theorem sharp_parent (R : ℝ) (l i j : Fin 4) (u g h : C(cube R,ℝ)) (q : FourMomenta) :
    CoareaNormalization.sharpReadout R (parentTest R l i j u g h) q=
      rawWeight R (twoWeight R i j g h) q*zeroExtension R u (q l) := by
  by_cases hq : q∈CoareaNormalization.allFourFlags R
  · rw [CoareaNormalization.sharpReadout,Set.indicator_of_mem hq,
      rawWeight_inside R _ hq,zeroExtension_apply R u ⟨q l,hq l⟩]
    simp only [parentTest,pointParent_apply,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
      Matrix.cons_val_zero,Matrix.cons_val_succ,zeroEval_inside R u (hq l),
      zeroEval_inside R g (hq i),zeroEval_inside R h (hq j)]
    change u ⟨q l,hq l⟩*(g ⟨q i,hq i⟩*h ⟨q j,hq j⟩)=
      (g ⟨q i,hq i⟩*h ⟨q j,hq j⟩)*u ⟨q l,hq l⟩
    ring
  · rw [CoareaNormalization.sharpReadout,Set.indicator_of_notMem hq,
      rawWeight_outside R _ hq,zero_mul]

theorem incoming_parent_output (R : ℝ) (i j : Fin 4) (u g h : C(cube R,ℝ)) (k : E) :
    incomingOutput R (parentTest R 1 i j u g h) k=
      ∫p,(‖k-p‖/8)*(∫σ,rawWeight R (twoWeight R i j g h)
        (IncomingPairMarginal.incomingQuartet ((k,p),σ))∂surface)*zeroExtension R u p∂cubeVolume R := by
  have he (p : E) : (∫σ:Sphere,incomingIntegrand R (parentTest R 1 i j u g h) ((k,p),σ)∂surface)=
      (‖k-p‖/8)*(∫σ,rawWeight R (twoWeight R i j g h)
        (IncomingPairMarginal.incomingQuartet ((k,p),σ))∂surface)*zeroExtension R u p := by
    simp only [incomingIntegrand,sharp_parent]
    change (∫σ:Sphere,(‖k-p‖/8)*(rawWeight R (twoWeight R i j g h)
      (IncomingPairMarginal.incomingQuartet ((k,p),σ))*zeroExtension R u p)∂surface)=_
    simp only [←mul_assoc,integral_mul_const,integral_const_mul]
  simp only [incomingOutput,he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  rw [zeroExtension_outside R u hp,mul_zero]

theorem cross_parent_output {R : ℝ} (hR : 0≤R) (i j : Fin 4)
    (u g h : C(cube R,ℝ)) (k : E) :
    crossOutput R (parentTest R 2 i j u g h) k=
      ∫p,(2*‖p-k‖)⁻¹*(∫z,rawWeight R (twoWeight R i j g h)
        (CrossPairCoordinates.crossQuartet ((k,p),z))∂CrossRowPointwise.finitePlaneMeasure R)*
          zeroExtension R u p∂cubeVolume R := by
  have he (p : E) : (∫z:PlaneCoarea.E2,crossIntegrand R (parentTest R 2 i j u g h) ((k,p),z))=
      (2*‖p-k‖)⁻¹*(∫z,rawWeight R (twoWeight R i j g h)
        (CrossPairCoordinates.crossQuartet ((k,p),z))∂CrossRowPointwise.finitePlaneMeasure R)*
          zeroExtension R u p := by
    simp only [SignedFiberReadout.crossIntegrand,integral_const_mul]
    change (2*‖p-k‖)⁻¹*CrossRowPointwise.planeIntegral R (parentTest R 2 i j u g h) k p=_
    rw [CrossRowPointwise.planeIntegral_box hR]
    simp only [sharp_parent,CrossPairCoordinates.crossQuartet_third,integral_mul_const,mul_assoc]
  simp only [crossOutput,he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  rw [zeroExtension_outside R u hp,mul_zero]

theorem incoming_parent_embed {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    embed R (parent R hR.le 1 i j u g h)=incomingReadout hR i j u g h := by
  have hf := ae_restrict_of_ae (s:=cube R) (original_incoming_fiber_ae hR.le
    (by positivity : 0≤‖u‖*‖g‖*‖h‖) (parentTest R 1 i j u g h)
      (parentTest_measurable R 1 i j u g h) (fun q _=>parentTest_bound R 1 i j u g h q))
  apply Lp.ext
  filter_upwards [embed_ae R (parent R hR.le 1 i j u g h),
    incomingReadout_ae hR i j u g h,hf,ae_restrict_mem (measurable_cube R)] with k he hr hf hk
  rw [he,zeroExtension_apply R _ ⟨k,hk⟩,hr]
  change fiberOutput R (parentTest R 1 i j u g h) k=_
  exact hf.trans (incoming_parent_output R i j u g h k)

theorem cross_parent_embed {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    embed R (parent R hR.le 2 i j u g h)=crossReadout hR i j u g h := by
  have hf := ae_restrict_of_ae (s:=cube R) (original_cross_fiber_ae hR.le
    (by positivity : 0≤‖u‖*‖g‖*‖h‖) (parentTest R 2 i j u g h)
      (parentTest_measurable R 2 i j u g h) (fun q _=>parentTest_bound R 2 i j u g h q))
  apply Lp.ext
  filter_upwards [embed_ae R (parent R hR.le 2 i j u g h),
    crossReadout_ae hR i j u g h,hf,ae_restrict_mem (measurable_cube R)] with k he hr hf hk
  rw [he,zeroExtension_apply R _ ⟨k,hk⟩,hr]
  change fiberOutput R (parentTest R 2 i j u g h) k=_
  exact hf.trans (cross_parent_output hR.le i j u g h k)

theorem incoming_parent_bound {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    ‖parent R hR.le 1 i j u g h‖≤
      ActualPairWeightLinear.rowBound hR*‖referenceContinuous hR.le*u‖*‖g‖*‖h‖ := by
  rw [←CubeContinuousEssentialNorm.embed_norm_eq hR,incoming_parent_embed hR]
  exact incomingReadout_bound hR i j u g h

theorem cross_parent_bound {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    ‖parent R hR.le 2 i j u g h‖≤
      ActualPairWeightLinear.rowBound hR*‖referenceContinuous hR.le*u‖*‖g‖*‖h‖ := by
  rw [←CubeContinuousEssentialNorm.embed_norm_eq hR,cross_parent_embed hR]
  exact crossReadout_bound hR i j u g h

def outgoingLeg : Fin 4→Fin 4 := ![0,1,3,2]

theorem outgoingLeg_apply (q : FourMomenta) (i : Fin 4) :
    swapOutgoingK q i=q (outgoingLeg i) := by fin_cases i <;> rfl

theorem parentTest_outgoing (R : ℝ) (l i j : Fin 4) (u g h : C(cube R,ℝ)) :
    parentTest R (outgoingLeg l) (outgoingLeg i) (outgoingLeg j) u g h=
      (parentTest R l i j u g h) ∘ swapOutgoingK := by
  funext q
  simp only [parentTest,pointParent_apply,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Function.comp_apply,outgoingLeg_apply]

theorem parent_outgoing {R : ℝ} (hR : 0<R) (l i j : Fin 4) (u g h : C(cube R,ℝ)) :
    parent R hR.le (outgoingLeg l) (outgoingLeg i) (outgoingLeg j) u g h=
      parent R hR.le l i j u g h := by
  have hf := ae_restrict_of_ae (s:=cube R) (original_outgoing_fiber_ae hR.le
    (by positivity : 0≤‖u‖*‖g‖*‖h‖) (parentTest R l i j u g h)
      (parentTest_measurable R l i j u g h) (fun q _=>parentTest_bound R l i j u g h q))
  rw [←parentTest_outgoing] at hf
  apply CubeContinuousEssentialNorm.continuous_ae_eq hR
  filter_upwards [hf,ae_restrict_mem (measurable_cube R)] with k hf hk
  rw [zeroExtension_apply R _ ⟨k,hk⟩,zeroExtension_apply R _ ⟨k,hk⟩]
  exact hf

theorem outgoing_parent_bound {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    ‖parent R hR.le 3 i j u g h‖≤
      ActualPairWeightLinear.rowBound hR*‖referenceContinuous hR.le*u‖*‖g‖*‖h‖ := by
  rw [←parent_outgoing hR 3 i j u g h]
  exact cross_parent_bound hR (outgoingLeg i) (outgoingLeg j) u g h

theorem geometric_le_reference {R : ℝ} (hR : 0≤R) (k : cube R) :
    CollisionFrequency.geometricFrequency R k≤(1+9*R^2)^3*CollisionFrequency.referenceFrequency R k := by
  have h := mul_le_mul_of_nonneg_left (CollisionFrequency.referenceFrequency_geometric_bounds hR k.property).1
    (show 0≤(1+9*R^2)^3 by positivity)
  simpa only [←mul_assoc,←mul_pow,mul_inv_cancel₀ (by positivity : (1+9*R^2)≠0),one_pow,one_mul] using h

theorem output_parent_bound {R : ℝ} (hR : 0≤R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    ‖parent R hR 0 i j u g h‖≤(1+9*R^2)^3*‖referenceContinuous hR*u‖*‖g‖*‖h‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro k
  letI := CollisionFiber.collisionKernel_finite hR
  haveI : IsFiniteMeasure (CollisionFiber.fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (CollisionFiber.collisionKernel R k))
  have hb : ∀ᵐq∂CollisionFiber.fiberMeasure R k,
      ‖parentTest R 0 i j u g h q‖≤‖u k‖*‖g‖*‖h‖ := by
    filter_upwards [CollisionFiber.fiber_support R k] with q hq
    simp only [parentTest,pointParent_apply,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
      Matrix.cons_val_zero,Matrix.cons_val_succ,norm_mul]
    rw [hq.2,zeroEval_inside R u k.property]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul (zeroEval_norm_le R g (q i)) (zeroEval_norm_le R h (q j))
        (norm_nonneg (zeroEval R (q j) h)) (norm_nonneg g)) (norm_nonneg (u k))
  change ‖∫q,parentTest R 0 i j u g h q∂CollisionFiber.fiberMeasure R k‖≤_
  have hn := norm_integral_le_of_norm_le_const hb
  rw [measureReal_def,←CollisionFrequency.geometricFrequency_eq_mass] at hn
  have hν : 0≤CollisionFrequency.referenceFrequency R k :=
    CrossRowWeightedBounds.referenceFrequency_nonnegative R k
  have hw : CollisionFrequency.referenceFrequency R k*‖u k‖≤‖referenceContinuous hR*u‖ := by
    simpa only [ContinuousMap.mul_apply,referenceContinuous,ContinuousMap.coe_mk,norm_mul,
      Real.norm_eq_abs,abs_of_nonneg hν] using (referenceContinuous hR*u).norm_coe_le_norm k
  calc
    _ ≤ (‖u k‖*‖g‖*‖h‖)*CollisionFrequency.geometricFrequency R k := hn
    _ ≤ (‖u k‖*‖g‖*‖h‖)*((1+9*R^2)^3*CollisionFrequency.referenceFrequency R k) :=
      mul_le_mul_of_nonneg_left (geometric_le_reference hR k) (by positivity)
    _ = ((1+9*R^2)^3*‖g‖*‖h‖)*(CollisionFrequency.referenceFrequency R k*‖u k‖) := by ring
    _ ≤ ((1+9*R^2)^3*‖g‖*‖h‖)*‖referenceContinuous hR*u‖ :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

def oneYConstant {R : ℝ} (hR : 0<R) : ℝ :=
  (1+9*R^2)^3+ActualPairWeightLinear.rowBound hR

theorem oneYConstant_positive {R : ℝ} (hR : 0<R) : 0<oneYConstant hR :=
  add_pos_of_pos_of_nonneg (by positivity) (ActualPairWeightLinear.rowBound_nonnegative hR)

theorem parent_oneY_bound {R : ℝ} (hR : 0<R) (l i j : Fin 4) (u g h : C(cube R,ℝ)) :
    ‖parent R hR.le l i j u g h‖≤oneYConstant hR*‖referenceContinuous hR.le*u‖*‖g‖*‖h‖ := by
  have h0 : (1+9*R^2)^3≤oneYConstant hR :=
    le_add_of_nonneg_right (ActualPairWeightLinear.rowBound_nonnegative hR)
  have h1 : ActualPairWeightLinear.rowBound hR≤oneYConstant hR := le_add_of_nonneg_left (by positivity)
  have hn : 0≤‖referenceContinuous hR.le*u‖*‖g‖*‖h‖ := by positivity
  have hh0 := mul_le_mul_of_nonneg_right h0 hn
  have hh1 := mul_le_mul_of_nonneg_right h1 hn
  simp only [←mul_assoc] at hh0 hh1
  fin_cases l
  · exact (output_parent_bound hR.le i j u g h).trans hh0
  · exact (incoming_parent_bound hR i j u g h).trans hh1
  · exact (cross_parent_bound hR i j u g h).trans hh1
  · exact (outgoing_parent_bound hR i j u g h).trans hh1

end
end Resonance.OneWeightedParent
