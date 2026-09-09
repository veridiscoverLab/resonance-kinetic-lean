import Resonance.PinnedTorusPermutations
import Resonance.BoxShrinkingKernel

/-! The exact full coarea-current exchange law follows from the original
Haar integral and the proved complete-difference limit. The auxiliary box
kernel is explicit; no shear is declared Euclidean-area preserving. -/
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Resonance.PinnedCoareaCurrentSymmetry
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedMeasureNormalization PinnedClassificationFinal
open PinnedMaximalDifference PinnedSmoothDomain PinnedCircleMollifier PinnedTorusPermutations
open BoxShrinkingKernel
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem box_energy_transform (j : Fin 3) (d η : ℝ) (k : CircleMomenta) :
    kernel η (energy d (transform j k))=kernel η (energy d k) := by
  rw [energy_transform]
  fin_cases j <;> simp [sign,kernel_neg]

theorem current_transform {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ))
    {W : CircleMomenta→ℂ} (hW : Continuous W) (j : Fin 3) :
    (∫k,W k*difference φ k ∂euclideanCircleRegularCoarea d)=
      (sign j:ℂ)*(∫k,W (transform j k)*difference φ k ∂euclideanCircleRegularCoarea d) := by
  have hroot (V : CircleMomenta→ℂ) (hV : Continuous V) :=
    (complete_source_limit hd0 hdU hφ hφ2 hV kernel
      (fun η _=>kernel_measurable η) (fun η _=>kernel_integrable η)
      (fun _ hη=>kernel_nonneg hη) (fun _ hη=>kernel_mass hη)
      (fun _ _ _ hq=>kernel_support hq)).2.2
  have h1 := hroot W hW
  have h2 := (tendsto_const_nhds (x:=(sign j:ℂ))).mul
    (hroot (W ∘ transform j) (hW.comp (transform_continuous j)))
  have he : ∀η:ℝ,(∫k,kernel η (energy d k) • (W k*difference φ k)
      ∂Measure.pi (fun _:Fin 3=>circleHaar))=
      (sign j:ℂ)*(∫k,kernel η (energy d k) • (W (transform j k)*difference φ k)
        ∂Measure.pi (fun _:Fin 3=>circleHaar)) := by
    intro η
    rw [←(transform_preserving j).integral_comp (equivalence j).toHomeomorph.measurableEmbedding]
    calc
      _ = ∫k,(sign j:ℂ)*(kernel η (energy d k) • (W (transform j k)*difference φ k))
          ∂Measure.pi (fun _:Fin 3=>circleHaar) := by
        apply integral_congr_ae
        filter_upwards [] with k
        simp only [box_energy_transform,difference_transform,Complex.real_smul]
        ring
      _ = _ := integral_const_mul _ _
  exact tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall (fun η=>(he η).symm)))

end
end Resonance.PinnedCoareaCurrentSymmetry
