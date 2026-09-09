import Resonance.SpatialThirdGN
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.Order.Chebyshev

/-! Mixed second-order GN on the original periodic spatial domain.
The Hessian symmetry is derived from the actual compatible kinetic jet,
not imposed on an independent collection of derivative fields. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.MixedSpatialGN
noncomputable section
open FreeTransport SpatialChainRule SpatialJetSpace SpatialTranslationOrbit
open SpatialIntegrationByParts SpatialThirdGN
set_option maxHeartbeats 1500000

theorem actual_second_symmetric {R : ℝ} (p : JetSpace R)
    (X : SpatialTorus) (a b : RealPosition) :
    p.val.2.2.1 X a b=p.val.2.2.1 X b a := by
  obtain ⟨x,rfl⟩:=torusQuotient_surjective X
  have hs:=((compatible_contDiff p.property).1.contDiffAt (x:=x)).isSymmSndFDerivAt
    (by norm_num [minSmoothness])
  simpa only [compatible_second_fderiv p.property] using hs a b

theorem actual_second_polarization {R : ℝ} (p : JetSpace R)
    (X : SpatialTorus) (k : MomentumDomain R) (a b : RealPosition) :
    2*p.val.2.2.1 X a b k=
      p.val.2.2.1 X (a+b) (a+b) k-p.val.2.2.1 X a a k-p.val.2.2.1 X b b k := by
  simp only [map_add,ContinuousLinearMap.add_apply,ContinuousMap.add_apply]
  rw [actual_second_symmetric p X b a]
  ring

theorem triple_sum_cube_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a+b+c)^3 ≤ 27*(a^3+b^3+c^3) := by
  let m:=max a (max b c)
  have hm : 0 ≤ m:=ha.trans (le_max_left _ _)
  have hsum : a+b+c ≤ 3*m := by
    have h1 : a ≤ m:=le_max_left _ _
    have h2 : b ≤ m:=(le_max_left _ _).trans (le_max_right _ _)
    have h3 : c ≤ m:=(le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hm3 : m^3 ≤ a^3+b^3+c^3 := by
    rcases le_total b c with hbc|hcb
    · dsimp only [m]
      rw [max_eq_right hbc]
      rcases le_total a c with hac|hca
      · rw [max_eq_right hac]; linarith [pow_nonneg ha 3,pow_nonneg hb 3]
      · rw [max_eq_left hca]; linarith [pow_nonneg hb 3,pow_nonneg hc 3]
    · dsimp only [m]
      rw [max_eq_left hcb]
      rcases le_total a b with hab|hba
      · rw [max_eq_right hab]; linarith [pow_nonneg ha 3,pow_nonneg hc 3]
      · rw [max_eq_left hba]; linarith [pow_nonneg hb 3,pow_nonneg hc 3]
  calc
    (a+b+c)^3 ≤ (3*m)^3:=pow_le_pow_left₀ (by positivity) hsum 3
    _ =27*m^3:=by ring
    _ ≤27*(a^3+b^3+c^3):=mul_le_mul_of_nonneg_left hm3 (by norm_num)

theorem polarization_cube_bound {x u v w : ℝ} (hx : 2*x=u-v-w) :
    |x|^3 ≤ 27*(|u|^3+|v|^3+|w|^3) := by
  have h2 : 2*|x| ≤ |u|+|v|+|w| := by
    calc
      2*|x|=|2*x|:=by rw [abs_mul]; norm_num
      _ =|u-v-w|:=congrArg abs hx
      _ ≤|u-v|+|w|:=abs_sub _ _
      _ ≤(|u|+|v|)+|w|:=by linarith [abs_sub u v]
  have hx1 : |x| ≤ |u|+|v|+|w|:=by linarith [abs_nonneg x]
  exact (pow_le_pow_left₀ (abs_nonneg x) hx1 3).trans
    (triple_sum_cube_le (abs_nonneg u) (abs_nonneg v) (abs_nonneg w))

def secondSection {R : ℝ} (p : JetSpace R) (k : MomentumDomain R)
    (a b : RealPosition) : ScalarField:=
  ⟨fun X=>p.val.2.2.1 X a b k,by fun_prop⟩

def thirdSection {R : ℝ} (p : JetSpace R) (k : MomentumDomain R)
    (a : RealPosition) : ScalarField:=
  ⟨fun X=>p.val.2.2.2 X a a a k,by fun_prop⟩

/-- All mixed second directions of the same actual kinetic jet are
controlled using only its zero and third spatial derivatives. -/
theorem actual_jet_mixed_second_GN {R : ℝ} (p : JetSpace R)
    (k : MomentumDomain R) (a b : RealPosition) :
    (∫X,|p.val.2.2.1 X a b k|^3) ≤ 540*‖scalarSection p k‖*
      ((∫X,(p.val.2.2.2 X (a+b) (a+b) (a+b) k)^2)+
       (∫X,(p.val.2.2.2 X a a a k)^2)+(∫X,(p.val.2.2.2 X b b b k)^2)) := by
  have hp : integralCLM ((absField (secondSection p k a b))^3) ≤
      27*(integralCLM ((absField (secondSection p k (a+b) (a+b)))^3)+
        integralCLM ((absField (secondSection p k a a))^3)+
        integralCLM ((absField (secondSection p k b b))^3)) := by
    have h:=integral_mono (scalar_integrable ((absField (secondSection p k a b))^3))
      (scalar_integrable ((27:ℝ) • (((absField (secondSection p k (a+b) (a+b)))^3)+
        ((absField (secondSection p k a a))^3)+((absField (secondSection p k b b))^3))))
      (fun X=>polarization_cube_bound (actual_second_polarization p X k a b))
    change integralCLM ((absField (secondSection p k a b))^3) ≤
      integralCLM ((27:ℝ) • (((absField (secondSection p k (a+b) (a+b)))^3)+
        ((absField (secondSection p k a a))^3)+((absField (secondSection p k b b))^3))) at h
    simpa only [map_add,map_smul,smul_eq_mul] using h
  have h1:=(actual_jet_directional_third_GN p k (a+b)).2
  have h2:=(actual_jet_directional_third_GN p k a).2
  have h3:=(actual_jet_directional_third_GN p k b).2
  change (∫X,|p.val.2.2.1 X a b k|^3) ≤
    27*((∫X,|p.val.2.2.1 X (a+b) (a+b) k|^3)+
      (∫X,|p.val.2.2.1 X a a k|^3)+(∫X,|p.val.2.2.1 X b b k|^3)) at hp
  nlinarith

def coordinate (i : Fin 3) : RealPosition:=Pi.single i 1

def thirdCoordinateSquare {R : ℝ} (p : JetSpace R) (X : SpatialTorus)
    (k : MomentumDomain R) : ℝ:=
  ∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,
    (p.val.2.2.2 X (coordinate i) (coordinate j) (coordinate l) k)^2

theorem thirdCoordinateSquare_nonneg {R : ℝ} (p : JetSpace R)
    (X : SpatialTorus) (k : MomentumDomain R) : 0 ≤ thirdCoordinateSquare p X k := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro l _
  exact sq_nonneg _

theorem third_component_square_le {R : ℝ} (p : JetSpace R)
    (X : SpatialTorus) (k : MomentumDomain R) (i j l : Fin 3) :
    (p.val.2.2.2 X (coordinate i) (coordinate j) (coordinate l) k)^2 ≤
      thirdCoordinateSquare p X k := by
  apply (Finset.single_le_sum (fun m _=>sq_nonneg
    (p.val.2.2.2 X (coordinate i) (coordinate j) (coordinate m) k)) (Finset.mem_univ l)).trans
  apply (Finset.single_le_sum (fun m _=>Finset.sum_nonneg (fun n _=>sq_nonneg
    (p.val.2.2.2 X (coordinate i) (coordinate m) (coordinate n) k))) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun m _=>Finset.sum_nonneg (fun n _=>
    Finset.sum_nonneg (fun o _=>sq_nonneg
      (p.val.2.2.2 X (coordinate m) (coordinate n) (coordinate o) k)))) (Finset.mem_univ i)

theorem eight_square (f : Fin 8 → ℝ) : (∑i,f i)^2 ≤ 8*∑i,(f i)^2 := by
  simpa using (sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=f))

theorem third_pair_direction_square_le {R : ℝ} (p : JetSpace R)
    (X : SpatialTorus) (k : MomentumDomain R) (i j : Fin 3) :
    (p.val.2.2.2 X (coordinate i+coordinate j) (coordinate i+coordinate j)
      (coordinate i+coordinate j) k)^2 ≤ 64*thirdCoordinateSquare p X k := by
  let t:Fin 3→Fin 3→Fin 3→ℝ:=fun a b d=>
    p.val.2.2.2 X (coordinate a) (coordinate b) (coordinate d) k
  have h:=eight_square ![t i i i,t i i j,t i j i,t i j j,t j i i,t j i j,t j j i,t j j j]
  have he : (p.val.2.2.2 X (coordinate i+coordinate j) (coordinate i+coordinate j)
      (coordinate i+coordinate j) k)^2 ≤
      8*((t i i i)^2+(t i i j)^2+(t i j i)^2+(t i j j)^2+
        (t j i i)^2+(t j i j)^2+(t j j i)^2+(t j j j)^2) := by
    simp only [map_add,ContinuousLinearMap.add_apply,ContinuousMap.add_apply]
    convert h using 1 <;> simp [Fin.sum_univ_succ,t] <;> ring
  have h1:=third_component_square_le p X k i i i
  have h2:=third_component_square_le p X k i i j
  have h3:=third_component_square_le p X k i j i
  have h4:=third_component_square_le p X k i j j
  have h5:=third_component_square_le p X k j i i
  have h6:=third_component_square_le p X k j i j
  have h7:=third_component_square_le p X k j j i
  have h8:=third_component_square_le p X k j j j
  dsimp only [t] at he
  linarith

def thirdCoordinateMass {R : ℝ} (p : JetSpace R) (k : MomentumDomain R) : ℝ:=
  ∫X,thirdCoordinateSquare p X k

theorem thirdCoordinateSquare_integrable {R : ℝ} (p : JetSpace R)
    (k : MomentumDomain R) : Integrable (fun X=>thirdCoordinateSquare p X k) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold thirdCoordinateSquare
    fun_prop
  · exact HasCompactSupport.of_compactSpace _

/-- Coordinate-form third GN, on exactly the original 27 ordered third
derivatives. The constants do not depend on the momentum or any k-derivative. -/
theorem actual_coordinate_GN {R : ℝ} (p : JetSpace R)
    (k : MomentumDomain R) (i j : Fin 3) :
    (∫X,(p.val.2.1 X (coordinate i) k)^6) ≤
      2500*‖scalarSection p k‖^4*thirdCoordinateMass p k ∧
    (∫X,|p.val.2.2.1 X (coordinate i) (coordinate j) k|^3) ≤
      35640*‖scalarSection p k‖*thirdCoordinateMass p k := by
  have hi : (∫X,(p.val.2.2.2 X (coordinate i) (coordinate i) (coordinate i) k)^2) ≤
      thirdCoordinateMass p k :=
    integral_mono (scalar_integrable ((thirdSection p k (coordinate i))^2))
      (thirdCoordinateSquare_integrable p k) (fun X=>third_component_square_le p X k i i i)
  have hj : (∫X,(p.val.2.2.2 X (coordinate j) (coordinate j) (coordinate j) k)^2) ≤
      thirdCoordinateMass p k :=
    integral_mono (scalar_integrable ((thirdSection p k (coordinate j))^2))
      (thirdCoordinateSquare_integrable p k) (fun X=>third_component_square_le p X k j j j)
  have hij : (∫X,(p.val.2.2.2 X (coordinate i+coordinate j) (coordinate i+coordinate j)
      (coordinate i+coordinate j) k)^2) ≤ 64*thirdCoordinateMass p k := by
    have h:=integral_mono (scalar_integrable
      ((thirdSection p k (coordinate i+coordinate j))^2))
      ((thirdCoordinateSquare_integrable p k).const_mul 64)
      (fun X=>third_pair_direction_square_le p X k i j)
    simpa only [integral_const_mul,thirdCoordinateMass] using h
  constructor
  · exact (actual_jet_directional_third_GN p k (coordinate i)).1.trans
      (mul_le_mul_of_nonneg_left hi (by positivity))
  · have h:=actual_jet_mixed_second_GN p k (coordinate i) (coordinate j)
    have hs : (∫X,(p.val.2.2.2 X (coordinate i+coordinate j) (coordinate i+coordinate j)
        (coordinate i+coordinate j) k)^2)+
        (∫X,(p.val.2.2.2 X (coordinate i) (coordinate i) (coordinate i) k)^2)+
        (∫X,(p.val.2.2.2 X (coordinate j) (coordinate j) (coordinate j) k)^2) ≤
        66*thirdCoordinateMass p k := by linarith
    have hb:=mul_le_mul_of_nonneg_left hs (show 0 ≤ 540*‖scalarSection p k‖ by positivity)
    nlinarith

end
end Resonance.MixedSpatialGN
