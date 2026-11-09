module

public import ArtinMatthews.SourceKPCuspPositiveHeightSupport
public import ArtinMatthews.SourceKPCuspNativeFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! The exact principal-cell Fourier mean of a continuous native
representative is continuous at every positive product height. -/

namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen Set
open scoped NumberField AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "P" => sourceKPCuspPositiveHeights K

def sourceKPCuspRepresentativeFourierCell (U : X → ℂ) (m : K) (y : V → ℝ) : ℂ :=
  ∫ x : I → ℝ, star (character K (algebraMap K 𝔸[K] m *
    sourceKPCuspUnitCellAdelicPoint K d hd x)) * U (E (x,y)) ∂unitTorusUnitCellMeasure I

theorem sourceKPCuspRepresentativeFourierCell_continuousOn_compact
    (U : X → ℂ) (hU : ContinuousOn U (productUpper V)) (m : K)
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : B ⊆ P) :
    ContinuousOn (sourceKPCuspRepresentativeFourierCell K hζ d hd U m) B := by
  let A := Icc (0 : I → ℝ) 1
  let S := Set.univ.pi (fun _ : I => Ioc (0 : ℝ) 1)
  let M := unitTorusUnitCellMeasure I
  let F (p : (I → ℝ) × (V → ℝ)) :=
    star (sourceKPCuspNativeFrequency K hζ d hd m (E p)) * U (E p)
  have hF : ContinuousOn F (A ×ˢ B) := by
    apply ContinuousOn.mul
    · exact (continuous_star.comp
        ((sourceKPCuspNativeFrequency_continuous K hζ d hd m).comp (E).continuous)).continuousOn
    · exact hU.comp (E).continuous.continuousOn (fun p hp =>
        sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos ⟨p, hp, rfl⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hB).exists_bound_of_continuousOn hF
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hSA : S ⊆ A := by
    intro x hx
    exact ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2⟩
  have hM : M = (volume : Measure (I → ℝ)).restrict S := by
    symm
    exact Measure.restrict_pi_pi _ _
  let _ : IsFiniteMeasure M := ⟨by
    change unitTorusUnitCellMeasure I univ < ⊤
    rw [unitTorusUnitCellMeasure, Measure.pi_univ]
    simp⟩
  have hAE : ∀ᵐ x ∂M, x ∈ S := hM ▸ ae_restrict_mem hS
  have hcont : ContinuousOn (fun y => ∫ x, F (x,y) ∂M) B := by
    apply continuousOn_of_dominated (bound := fun _ : I → ℝ => C)
    · intro y hy
      rw [hM]
      exact (hF.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => show (x,y) ∈ A ×ˢ B from ⟨hSA hx,hy⟩)).aestronglyMeasurable hS
    · intro y hy
      exact hAE.mono fun x hx => hC (x,y) ⟨hSA hx,hy⟩
    · exact integrable_const C
    · exact hAE.mono fun x hx => hF.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun y hy => show (x,y) ∈ A ×ˢ B from ⟨hSA hx,hy⟩)
  unfold sourceKPCuspRepresentativeFourierCell
  simpa only [F, M, sourceKPCuspNativeFrequency_coordinates] using hcont

theorem sourceKPCuspRepresentativeFourierCell_continuousOn
    (U : X → ℂ) (hU : ContinuousOn U (productUpper V)) (m : K) :
    ContinuousOn (sourceKPCuspRepresentativeFourierCell K hζ d hd U m) P := by
  intro y hy
  obtain ⟨B, hBc, hBy, hBP⟩ := sourceKPCuspPositiveHeights_compact_nhds K y hy
  exact (((sourceKPCuspRepresentativeFourierCell_continuousOn_compact K hζ d hd U hU m B hBc hBP)
    y (mem_of_mem_nhds hBy)).continuousAt hBy).continuousWithinAt

end
end ArtinMatthews
