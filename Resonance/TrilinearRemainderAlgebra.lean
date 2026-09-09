import Resonance.NormalizedCubicOneY

/-! Exact three-slot algebra used on the original normalized collision.
No symmetry between the three input functions is assumed. -/
open Function
open scoped BigOperators
namespace Resonance.TrilinearRemainderAlgebra
noncomputable section
set_option maxHeartbeats 1200000
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3=>X) Y)

theorem add_first (a b c d : X) : T ![a+b,c,d]=T ![a,c,d]+T ![b,c,d] := by
  have hv (t : X) : update ![a,c,d] 0 t=![t,c,d] := by ext i; fin_cases i <;> simp
  simpa only [hv] using T.map_update_add ![a,c,d] 0 a b

theorem add_second (a b c d : X) : T ![c,a+b,d]=T ![c,a,d]+T ![c,b,d] := by
  have hv (t : X) : update ![c,a,d] 1 t=![c,t,d] := by ext i; fin_cases i <;> simp
  simpa only [hv] using T.map_update_add ![c,a,d] 1 a b

theorem add_third (a b c d : X) : T ![c,d,a+b]=T ![c,d,a]+T ![c,d,b] := by
  have hv (t : X) : update ![c,d,a] 2 t=![c,d,t] := by ext i; fin_cases i <;> simp
  simpa only [hv] using T.map_update_add ![c,d,a] 2 a b

theorem sub_first (a b c d : X) : T ![a-b,c,d]=T ![a,c,d]-T ![b,c,d] := by
  have hv (t : X) : update ![a,c,d] 0 t=![t,c,d] := by ext i; fin_cases i <;> simp
  simpa only [hv] using T.map_update_sub ![a,c,d] 0 a b

theorem sub_second (a b c d : X) : T ![c,a-b,d]=T ![c,a,d]-T ![c,b,d] := by
  have hv (t : X) : update ![c,a,d] 1 t=![c,t,d] := by ext i; fin_cases i <;> simp
  simpa only [hv] using T.map_update_sub ![c,a,d] 1 a b

theorem sub_third (a b c d : X) : T ![c,d,a-b]=T ![c,d,a]-T ![c,d,b] := by
  have hv (t : X) : update ![c,d,a] 2 t=![c,d,t] := by ext i; fin_cases i <;> simp
  simpa only [hv] using T.map_update_sub ![c,d,a] 2 a b

def remainder (e q : X) : Y :=
  T ![q,q,e]+T ![q,e,q]+T ![e,q,q]+T ![q,q,q]

def linearPart (e q : X) : Y := T ![q,e,e]+T ![e,q,e]+T ![e,e,q]

theorem exact_expansion (e q : X) :
    T ![e+q,e+q,e+q]=T ![e,e,e]+linearPart T e q+remainder T e q := by
  simp only [add_first,add_second,add_third,linearPart,remainder]
  abel

def differenceTerms (e q r : X) : Fin 9→Y :=
  ![T ![q-r,q,e], T ![r,q-r,e], T ![q-r,e,q], T ![r,e,q-r],
    T ![e,q-r,q], T ![e,r,q-r],
    T ![q-r,q,q], T ![r,q-r,q], T ![r,r,q-r]]

theorem exact_difference (e q r : X) :
    remainder T e q-remainder T e r=∑i : Fin 9,differenceTerms T e q r i := by
  simp only [differenceTerms,remainder,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,sub_first,sub_second,sub_third]
  abel

theorem norm_difference_le {e q r : X} {B : ℝ}
    (h : ∀i : Fin 9,‖differenceTerms T e q r i‖≤B) :
    ‖remainder T e q-remainder T e r‖≤9*B := by
  rw [exact_difference]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _=>h i)).trans_eq (by simp))

end
end Resonance.TrilinearRemainderAlgebra
