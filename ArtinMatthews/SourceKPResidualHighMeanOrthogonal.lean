module

public import ArtinMatthews.SourceKPDefectHighMean
public import ArtinMatthews.SourceKPAutomorphicSpectralContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! The exact pole projection sends the defect to a residual vector
orthogonal to the high-mean-zero part of the exceptional eigenspace. -/

namespace ArtinMatthews
open NumberField MeasureTheory HilbertResolvent
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "V" => SourceKPCompactGenuineH1 K hζ
local notation "rK" => (InfinitePlace.nrComplexPlaces K : ℝ)

theorem sourceKPExceptionalResidue_inner_eq_zero_of_highMean_zero {T : ℝ} (hT : 2 < T)
    (v : V) (hv : v ∈ nullSpace ((j).adjoint.comp j) (exceptionalCenter rK))
    (hmean : ∀ᵐ x ∂(sourceKPHighRepresentativeHaar K hζ (T / 2)).restrict
        (sourceKPCuspBandHighSection K hζ (T / 2)),
      sourceKPCompactHighUnipotentMean K hζ (T / 2) ((j v).val : Y → ℂ) x = 0) :
    inner ℂ (j v) (sourceKPAutomorphicExceptionalResidue K hζ (by linarith : 1 ≤ T)) = 0 := by
  have hT1 : 1 ≤ T := by linarith
  let d := sourceKPAutomorphicGenuineDefectL2 K hζ hT1 (1 / 6)
  let P := nullSpace ((j).adjoint.comp j) (exceptionalCenter rK)
  have hd : inner ℂ (j v) d = 0 :=
    sourceKPGenuineDefect_inner_eq_zero_of_highMean_zero K hζ hT (1 / 6) (j v) hmean
  have hfix : P.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have hp : inner ℂ v (P.starProjection ((j).adjoint d)) = 0 := by
    rw [← P.inner_starProjection_left_eq_right v ((j).adjoint d), hfix,
      ContinuousLinearMap.adjoint_inner_right]
    exact hd
  have hne : exceptionalCenter rK + 1 ≠ 0 := by
    have hr := sourceKPAutomorphicSpectralRank_pos K hζ
    unfold exceptionalCenter
    linarith
  have hmass : inner ℂ (j v) (j (P.starProjection ((j).adjoint d))) = 0 := by
    rw [← (j).adjoint_inner_left (P.starProjection ((j).adjoint d)) (j v)]
    change inner ℂ (((j).adjoint.comp j) v) (P.starProjection ((j).adjoint d)) = 0
    rw [HilbertResolvent.apply_of_mem_null _ _ hne hv, inner_smul_left, hp, mul_zero]
  rw [← sourceKPAutomorphicExceptionalFormResidue_mass K hζ hT1,
    sourceKPAutomorphicExceptionalFormResidue, map_smul]
  let c : ℂ := -3 * ((exceptionalCenter rK : ℂ) + 1) / (4 * (rK : ℂ))
  let z : SourceKPGenuineAutomorphicL2 K hζ := j (P.starProjection ((j).adjoint d))
  change (innerSL ℂ (j v)) (c • z) = 0
  calc
    _ = c • (innerSL ℂ (j v)) z := (innerSL ℂ (j v)).map_smul c z
    _ = 0 := by
      change c • inner ℂ (j v) (j (P.starProjection ((j).adjoint d))) = 0
      rw [hmass, smul_zero]

end
end ArtinMatthews
