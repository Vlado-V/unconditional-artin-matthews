module

public import ArtinMatthews.SourceLocalMultiplicativeShell
public import ArtinMatthews.SourceKPJacquetFlatDiagonal
public import ArtinMatthews.SourceKPJacquetFrequencyCutoff
public import ArtinMatthews.SourceKPJacquetOpenBound
public import ArtinMatthews.SourceKPJacquetTinyUnits
public import ArtinMatthews.StandardLocalHaarScaling
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual diagonal Jacquet value has bounded multiplicative
support and small-norm exponent one third at the negative parameter. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "B" => sourceLocalBall K P
local notation "Q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "ν₀" => sourceLocalValuation K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "n₋" => fun t : L => l₀ (sourceGL2Lower t)
local notation "a₀" => fun t : Lˣ => l₀ (sourceGL2Diagonal t)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
    (hC : ∀ (g : SourceFiniteKP2Projective K hζ P) (f : sourceAlgebraicInducedSpace _ ρ),
      f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P) ρ g f ∈ C)
    (hUpper : ∀ t : P.adicCompletion K, ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelUpper K hζ P t) v = v)
    (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
local notation "r₀" => sourceKPJacquetRight K hζ P ρ C hC
local notation "hU" => sourceKPJacquet_unitCube_of_negativeCubeLaw K hζ P ρ hCube
local notation "J" => sourceKPJacquetStableMap K hζ P ρ C e hUpper hU hSmooth
local notation "D" => sourceKPJacquetFlatDiagonal K hζ P ρ
local notation "Fz" => sourceKPJacquetFrequencyTruncation K hζ P ρ e
local notation "R₀" => sourceKPJacquetFrequencyRadius K P

theorem sourceKPJacquetStableMap_diagonal_cutoff (f : C) (M N : ℕ)
    (hTiny : ∀ z : Lˣ, ((z : L) - 1) ∈ B (-(M : ℤ)) →
      ∃ w : Lˣ, z = w ^ 3 ∧ ν₀ (z : L) = 1)
    (hFix : ∀ t ∈ B (-(N : ℤ)), ∀ g : G,
      f.val.val (g * n₀ t) = f.val.val g ∧ f.val.val (g * n₋ t) = f.val.val g)
    (z : Lˣ) : J (r₀ (a₀ z) f) = (↑(‖(z : L)‖ ^ (2 / 3 : ℝ)) : ℂ) •
      D z⁻¹ (Fz z (R₀ M N z : ℤ) f.val) := by
  have hv := sourceKPJacquetFrequencyHasStableValue_cutoff K hζ P ρ hUpper hU e f.val M N hTiny hFix z
  exact (sourceKPJacquetStableMap_diagonal_of_frequency K hζ P ρ C e hC hUpper hU hSmooth z f _ hv).trans
    (sourceKPJacquet_diagonal_Haar_factor K hζ P ρ z _)

theorem sourceKPJacquetStableMap_diagonal_bounds (f : C) :
    ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → J (r₀ (a₀ z) f) = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 →
        ‖e (J (r₀ (a₀ z) f))‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ) := by
  obtain ⟨N, hN⟩ := hSmooth f
  obtain ⟨M, _, hTiny⟩ := sourceKPJacquet_tiny_unit_cube K P
  obtain ⟨A, hA, hFlat⟩ := sourceKPJacquetFlatDiagonal_norm_bound K hζ P ρ e hCube
  obtain ⟨T, hT, hTr⟩ := sourceKPJacquet_frequency_truncation_bound K hζ P ρ e hUpper hCube f.val N hN
  let U := (Q ^ (1 / 3 : ℝ)) ^ (sourceDifferentExponent K P + 1 + M + N)
  have hU0 : 0 < U := pow_pos (Real.rpow_pos_of_pos (sourceLocalNorm_pos K P) _) _
  have hEq (z : Lˣ) := sourceKPJacquetStableMap_diagonal_cutoff K hζ P ρ C e hC hUpper hCube hSmooth
    f M N hTiny hN z
  refine ⟨(sourceDifferentExponent K P : ℤ) + (N : ℤ), A * T * U, mul_pos (mul_pos hA hT) hU0, ?_, ?_⟩
  · intro z hz
    have hzero := sourceKPJacquetFrequencyTruncation_zero_of_large K hζ P ρ e z f.val N
      (fun t ht g => (hN t ht g).1) hz (R₀ M N z)
    rw [hEq z, hzero, map_zero, smul_zero]
  · intro z hz
    have hPow : 0 ≤ ‖(z : L)‖ ^ (2 / 3 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hr := sourceKPJacquetFrequencyRadius_pow_eq K P M N z hz
    calc
      _ = ‖(z : L)‖ ^ (2 / 3 : ℝ) * ‖e (D z⁻¹ (Fz z (R₀ M N z : ℤ) f.val))‖ := by
        rw [hEq z, map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hPow]
      _ ≤ ‖(z : L)‖ ^ (2 / 3 : ℝ) * (A * ‖e (Fz z (R₀ M N z : ℤ) f.val)‖) :=
        mul_le_mul_of_nonneg_left (hFlat z⁻¹ _) hPow
      _ ≤ ‖(z : L)‖ ^ (2 / 3 : ℝ) * (A * (T * (Q ^ (1 / 3 : ℝ)) ^ R₀ M N z)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hTr z (R₀ M N z)) hA.le) hPow
      _ = (A * T * U) * (‖(z : L)‖ ^ (2 / 3 : ℝ) * ‖(z : L)‖ ^ (-(1 / 3) : ℝ)) := by
        rw [hr]
        dsimp only [U]
        ring
      _ = _ := by
        rw [← Real.rpow_add (norm_pos_iff.mpr z.ne_zero)]
        norm_num

end
end ArtinMatthews
