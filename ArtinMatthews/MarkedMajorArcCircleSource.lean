module

public import ArtinMatthews.MarkedMajorCharacterActual
public import ArtinMatthews.MarkedMinorArcBanMajor
public import ArtinMatthews.MarkedMinorArcCleanKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Literal circle-frequency form of the determinant source and the original
major-kernel sum, with exact finite-sum/integral interchange. -/
namespace ArtinMatthews
open Finset MeasureTheory
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

def markedMajorCircleSource (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (Y : ℝ) (ξ : AddCircle (1:ℝ)) : ℂ :=
  ∑ z ∈ S,∑ z' ∈ T,A z*B z'*ψ ((markedMajorIntegerDeterminant z z':ℤ)/Y)*
    fourier (markedMajorIntegerDeterminant z z'-(z.1:ℤ)+(z'.1:ℤ)) ξ

def markedMajorKernelSource (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (Q Y : ℝ) : ℂ :=
  ∑ z ∈ S,∑ z' ∈ T,A z*B z'*ψ ((markedMajorIntegerDeterminant z z':ℤ)/Y)*
    markedBanMajorKernel Q Y (markedMajorIntegerDeterminant z z'-(z.1:ℤ)+(z'.1:ℤ))

 theorem markedMajor_fourier_phase (k : ℤ) (t : ℝ) :
    fourier k (t:AddCircle (1:ℝ)) = OAI.Problem337.RealPhase.phase (t*(k:ℝ)) := by
  rw [fourier_coe_apply]
  unfold OAI.Problem337.RealPhase.phase
  congr 1
  push_cast
  ring

 theorem markedMajorCircleSource_arc (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (q : ℕ) (h : ℤ) (θ Y : ℝ) :
    markedMajorCircleSource S T A B ψ Y ((((h:ℝ)/(q:ℝ)+θ/Y):ℝ):AddCircle (1:ℝ)) =
      markedMajorArcSourceSum S T A B ψ q h θ Y := by
  simp only [markedMajorCircleSource,markedMajorArcSourceSum,markedMajor_fourier_phase]

 theorem markedMajorCircleSource_continuous (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (Y : ℝ) :
    Continuous (markedMajorCircleSource S T A B ψ Y) := by
  unfold markedMajorCircleSource
  fun_prop

 theorem markedMajorCircleSource_integrable (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (Y : ℝ) :
    Integrable (markedMajorCircleSource S T A B ψ Y) AddCircle.haarAddCircle :=
  (markedMajorCircleSource_continuous S T A B ψ Y).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

 theorem markedMajorKernelSource_eq_integral (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) (Q Y : ℝ) :
    markedMajorKernelSource S T A B ψ Q Y =
      ∫ ξ : AddCircle (1:ℝ) in markedMinorCircleMajor Q Y,
        markedMajorCircleSource S T A B ψ Y ξ ∂AddCircle.haarAddCircle := by
  have hf (k : ℤ) : Integrable (fourier (T := (1:ℝ)) k) AddCircle.haarAddCircle :=
    (fourier (T := (1:ℝ)) k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold markedMajorKernelSource markedMajorCircleSource markedBanMajorKernel
  rw [integral_finsetSum S (fun z _ => integrable_finsetSum T
    (fun z' _ => ((hf _).const_mul _).integrableOn))]
  apply sum_congr rfl
  intro z _
  rw [integral_finsetSum T (fun z' _ => ((hf _).const_mul _).integrableOn)]
  apply sum_congr rfl
  intro z' _
  exact (integral_const_mul _ _).symm

end
end ArtinMatthews
