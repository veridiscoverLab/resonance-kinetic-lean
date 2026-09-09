import Resonance.JetSeminorm

/-! Triangular bounds for all actual cubic collision parents in the separate
spatial derivative seminorms. These bounds feed the same-solution Duhamel
inequality; the top derivative is linear once lower orders are controlled. -/
open Set
open scoped BigOperators
namespace Resonance.JetCollisionBounds
noncomputable section
open SpatialChainRule JetCollision JetSeminorm SpatialTranslationOrbit FreeTransport
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 50000

def partitionBound (A B : ℕ → ℝ) {n : ℕ} (d : OrderedFinpartition n) : ℝ :=
  A d.length * ∏ i,B (d.partSize i)

theorem partitionBound_one (A B : ℕ → ℝ) :
    (∑ d : OrderedFinpartition 1,partitionBound A B d)=A 1*B 1 := by
  rw [sum_partitions_one]
  simp [partitionBound,p1,OrderedFinpartition.extendLeft,OrderedFinpartition.atomic]

theorem partitionBound_two (A B : ℕ → ℝ) :
    (∑ d : OrderedFinpartition 2,partitionBound A B d)=A 2*(B 1)^2+A 1*B 2 := by
  rw [sum_partitions_two]
  change A 2*(∏ i : Fin 2,B (p2a.partSize i))+
    A 1*(∏ i : Fin 1,B (p2b.partSize i))=_
  rw [Fin.prod_univ_two,Fin.prod_univ_one]
  change A 2*(B 1*B 1)+A 1*B 2=A 2*(B 1)^2+A 1*B 2
  ring

theorem partitionBound_three (A B : ℕ → ℝ) :
    (∑ d : OrderedFinpartition 3,partitionBound A B d)=
      A 3*(B 1)^3+3*A 2*B 1*B 2+A 1*B 3 := by
  rw [sum_partitions_three]
  change A 3*(∏ i : Fin 3,B (p2a.extendLeft.partSize i))+
    A 2*(∏ i : Fin 2,B ((p2a.extendMiddle ⟨0,by decide⟩).partSize i))+
    A 2*(∏ i : Fin 2,B ((p2a.extendMiddle ⟨1,by decide⟩).partSize i))+
    A 2*(∏ i : Fin 2,B (p2b.extendLeft.partSize i))+
    A 1*(∏ i : Fin 1,B ((p2b.extendMiddle ⟨0,by decide⟩).partSize i))=_
  simp only [Fin.prod_univ_three,Fin.prod_univ_two,Fin.prod_univ_one]
  change A 3*(B 1*B 1*B 1)+A 2*(B 2*B 1)+A 2*(B 1*B 2)+
    A 2*(B 1*B 2)+A 1*B 3=A 3*(B 1)^3+3*A 2*B 1*B 2+A 1*B 3
  ring

section Composition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_taylorComp_le (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (n : ℕ) :
    ‖q.taylorComp p n‖ ≤ ∑ d : OrderedFinpartition n,
      partitionBound (fun i => ‖q i‖) (fun i => ‖p i‖) d := by
  unfold FormalMultilinearSeries.taylorComp
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  exact d.norm_compAlongOrderedFinpartition_le (q d.length) (fun i => p (d.partSize i))

theorem norm_second_composition {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt ℝ 2 g (f x)) (hf : ContDiffAt ℝ 2 f x) :
    ‖iteratedFDeriv ℝ 2 (g ∘ f) x‖ ≤
      ‖iteratedFDeriv ℝ 2 g (f x)‖ * ‖iteratedFDeriv ℝ 1 f x‖^2 +
      ‖iteratedFDeriv ℝ 1 g (f x)‖ * ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [iteratedFDeriv_comp hg hf (by rfl)]
  exact (norm_taylorComp_le _ _ 2).trans_eq (partitionBound_two _ _)

theorem norm_third_composition {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt ℝ 3 g (f x)) (hf : ContDiffAt ℝ 3 f x) :
    ‖iteratedFDeriv ℝ 3 (g ∘ f) x‖ ≤
      ‖iteratedFDeriv ℝ 3 g (f x)‖ * ‖iteratedFDeriv ℝ 1 f x‖^3 +
      3*‖iteratedFDeriv ℝ 2 g (f x)‖ * ‖iteratedFDeriv ℝ 1 f x‖ * ‖iteratedFDeriv ℝ 2 f x‖ +
      ‖iteratedFDeriv ℝ 1 g (f x)‖ * ‖iteratedFDeriv ℝ 3 f x‖ := by
  rw [iteratedFDeriv_comp hg hf (by rfl)]
  exact (norm_taylorComp_le _ _ 3).trans_eq (partitionBound_three _ _)

theorem norm_first_composition {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt ℝ 1 g (f x)) (hf : ContDiffAt ℝ 1 f x) :
    ‖iteratedFDeriv ℝ 1 (g ∘ f) x‖ ≤
      ‖iteratedFDeriv ℝ 1 g (f x)‖ * ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [iteratedFDeriv_comp hg hf (by rfl)]
  exact (norm_taylorComp_le _ _ 1).trans_eq (partitionBound_one _ _)

end Composition

def collisionConstant (R : ℝ) : ℝ := 4*(CollisionFiber.fiberMassBound R).toReal

theorem collisionConstant_nonnegative (R : ℝ) : 0 ≤ collisionConstant R := by
  unfold collisionConstant
  positivity

theorem orbit_zero (R : ℝ) (f : Distribution R) : distributionOrbit f 0=f := by
  ext z
  change f (torusQuotient 0+z.1,z.2)=f z
  have hz : torusQuotient (0 : RealPosition)=(0 : SpatialTorus) := by
    funext i
    simp [torusQuotient]
  rw [hz,zero_add]

theorem orbit_collision {R : ℝ} (hR : 0 ≤ R) (p : Space R) :
    distributionOrbit (readback (JetCollision.collision R hR p)) =
      SpatialCollision.collision R hR ∘ distributionOrbit (readback p) := by
  rw [collision_readback]
  funext x
  ext z
  rfl

theorem outer_first_bound {R : ℝ} (hR : 0 ≤ R) (f : Distribution R) :
    ‖iteratedFDeriv ℝ 1 (SpatialCollision.collision R hR) f‖ ≤
      3*collisionConstant R*‖f‖^2 := by
  simpa only [collisionConstant,show Nat.descFactorial 3 1=3 from rfl,
    Nat.cast_ofNat,show 3-1=2 from rfl] using
    SpatialCollisionJets.collision_iteratedFDeriv_norm_le hR 1 f

theorem outer_second_bound {R : ℝ} (hR : 0 ≤ R) (f : Distribution R) :
    ‖iteratedFDeriv ℝ 2 (SpatialCollision.collision R hR) f‖ ≤
      6*collisionConstant R*‖f‖ := by
  simpa only [collisionConstant,show Nat.descFactorial 3 2=6 from rfl,
    Nat.cast_ofNat,show 3-2=1 from rfl,pow_one] using
    SpatialCollisionJets.collision_iteratedFDeriv_norm_le hR 2 f

theorem outer_third_bound {R : ℝ} (hR : 0 ≤ R) (f : Distribution R) :
    ‖iteratedFDeriv ℝ 3 (SpatialCollision.collision R hR) f‖ ≤
      6*collisionConstant R := by
  simpa only [collisionConstant,show Nat.descFactorial 3 3=6 from rfl,
    Nat.cast_ofNat,Nat.sub_self,pow_zero,mul_one] using
    SpatialCollisionJets.collision_iteratedFDeriv_norm_le hR 3 f

theorem first_seminorm_collision {R : ℝ} (hR : 0 ≤ R) (p : Space R) :
    spatialSeminorm R 1 (by omega) (JetCollision.collision R hR p) ≤
      3*collisionConstant R*‖readback p‖^2*spatialSeminorm R 1 (by omega) p := by
  have h := norm_first_composition
    ((SpatialCollisionJets.collision_contDiff hR 1).contDiffAt)
    (((distributionOrbit_contDiff p).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt)
    (x := (0 : RealPosition))
  rw [orbit_zero] at h
  change ‖iteratedFDeriv ℝ 1 (distributionOrbit (readback (JetCollision.collision R hR p))) 0‖ ≤ _
  rw [orbit_collision]
  apply h.trans
  exact mul_le_mul_of_nonneg_right (outer_first_bound hR (readback p)) (norm_nonneg _)

theorem second_seminorm_collision {R : ℝ} (hR : 0 ≤ R) (p : Space R) :
    spatialSeminorm R 2 (by omega) (JetCollision.collision R hR p) ≤
      6*collisionConstant R*‖readback p‖*(spatialSeminorm R 1 (by omega) p)^2 +
      3*collisionConstant R*‖readback p‖^2*spatialSeminorm R 2 (by omega) p := by
  have h := norm_second_composition
    ((SpatialCollisionJets.collision_contDiff hR 2).contDiffAt)
    (((distributionOrbit_contDiff p).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt)
    (x := (0 : RealPosition))
  rw [orbit_zero] at h
  change ‖iteratedFDeriv ℝ 2 (distributionOrbit (readback (JetCollision.collision R hR p))) 0‖ ≤ _
  rw [orbit_collision]
  apply h.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_right (outer_second_bound hR (readback p)) (sq_nonneg _))
    (mul_le_mul_of_nonneg_right (outer_first_bound hR (readback p)) (norm_nonneg _))

/-- The highest spatial derivative appears linearly. The other full cubic
terms contain only orders one and two, including all three mixed partitions. -/
theorem third_seminorm_collision {R : ℝ} (hR : 0 ≤ R) (p : Space R) :
    spatialSeminorm R 3 (by omega) (JetCollision.collision R hR p) ≤
      6*collisionConstant R*(spatialSeminorm R 1 (by omega) p)^3 +
      18*collisionConstant R*‖readback p‖*spatialSeminorm R 1 (by omega) p*
        spatialSeminorm R 2 (by omega) p +
      3*collisionConstant R*‖readback p‖^2*spatialSeminorm R 3 (by omega) p := by
  have h := norm_third_composition
    ((SpatialCollisionJets.collision_contDiff hR 3).contDiffAt)
    ((distributionOrbit_contDiff p).contDiffAt) (x := (0 : RealPosition))
  rw [orbit_zero] at h
  change ‖iteratedFDeriv ℝ 3 (distributionOrbit (readback (JetCollision.collision R hR p))) 0‖ ≤ _
  rw [orbit_collision]
  apply h.trans
  have ha := outer_first_bound hR (readback p)
  have hb := outer_second_bound hR (readback p)
  have hc := outer_third_bound hR (readback p)
  have hK := collisionConstant_nonnegative R
  calc
    _ ≤ (6*collisionConstant R)*‖iteratedFDeriv ℝ 1 (distributionOrbit (readback p)) 0‖^3 +
      3*(6*collisionConstant R*‖readback p‖)*‖iteratedFDeriv ℝ 1 (distributionOrbit (readback p)) 0‖*
        ‖iteratedFDeriv ℝ 2 (distributionOrbit (readback p)) 0‖ +
      (3*collisionConstant R*‖readback p‖^2)*‖iteratedFDeriv ℝ 3 (distributionOrbit (readback p)) 0‖ := by
        dsimp only [readback] at ha hb hc ⊢
        gcongr
    _ = _ := by unfold spatialSeminorm; simp only [orbitDerivative_actual]; ring

end
end Resonance.JetCollisionBounds

#check Resonance.JetCollisionBounds.partitionBound_one
#print axioms Resonance.JetCollisionBounds.partitionBound_one
#check Resonance.JetCollisionBounds.partitionBound_two
#print axioms Resonance.JetCollisionBounds.partitionBound_two
#check Resonance.JetCollisionBounds.partitionBound_three
#print axioms Resonance.JetCollisionBounds.partitionBound_three
#check Resonance.JetCollisionBounds.norm_taylorComp_le
#print axioms Resonance.JetCollisionBounds.norm_taylorComp_le
#check Resonance.JetCollisionBounds.norm_second_composition
#print axioms Resonance.JetCollisionBounds.norm_second_composition
#check Resonance.JetCollisionBounds.norm_third_composition
#print axioms Resonance.JetCollisionBounds.norm_third_composition
#check Resonance.JetCollisionBounds.norm_first_composition
#print axioms Resonance.JetCollisionBounds.norm_first_composition
#check Resonance.JetCollisionBounds.collisionConstant_nonnegative
#print axioms Resonance.JetCollisionBounds.collisionConstant_nonnegative
#check Resonance.JetCollisionBounds.orbit_zero
#print axioms Resonance.JetCollisionBounds.orbit_zero
#check Resonance.JetCollisionBounds.orbit_collision
#print axioms Resonance.JetCollisionBounds.orbit_collision
#check Resonance.JetCollisionBounds.outer_first_bound
#print axioms Resonance.JetCollisionBounds.outer_first_bound
#check Resonance.JetCollisionBounds.outer_second_bound
#print axioms Resonance.JetCollisionBounds.outer_second_bound
#check Resonance.JetCollisionBounds.outer_third_bound
#print axioms Resonance.JetCollisionBounds.outer_third_bound
#check Resonance.JetCollisionBounds.first_seminorm_collision
#print axioms Resonance.JetCollisionBounds.first_seminorm_collision
#check Resonance.JetCollisionBounds.second_seminorm_collision
#print axioms Resonance.JetCollisionBounds.second_seminorm_collision
#check Resonance.JetCollisionBounds.third_seminorm_collision
#print axioms Resonance.JetCollisionBounds.third_seminorm_collision
