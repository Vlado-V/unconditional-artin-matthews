module

public import ArtinMatthews.MarkedMinorArcBanMajor
public import ArtinMatthews.MarkedMajorCharacterArc
public import ArtinMatthews.MarkedMinorArcEndpoints
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


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
