module

public import ArtinMatthews.SpectralCuspDoubleCosetRepresentatives
public import ArtinMatthews.AtkinLehnerMixedPhase
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The finite phase sum for the actual common-period N double cosets.
The denominator is N*c, matching the source frequencies m/N and n/N. -/

noncomputable section
open Set
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

def cuspGeometricPhase (N : ℕ) (m n c : ℤ) (M : SL(2, ℤ)) : ℂ :=
  atkinPhase (((m : ℝ) * (M 1 1 : ℝ) + (n : ℝ) * (M 0 0 : ℝ)) /
    ((N : ℝ) * c))

theorem cuspGeometricPhase_norm (N : ℕ) (m n c : ℤ) (M : SL(2, ℤ)) :
    ‖cuspGeometricPhase N m n c M‖ = 1 :=
  atkinPhase_norm _

theorem cuspGeometricPhase_period_translate (N : ℕ) [NeZero N]
    (m n c : ℤ) (hc : c ≠ 0) (M : SL(2, ℤ)) (hM : M 1 0 = c) (l k : ℤ) :
    cuspGeometricPhase N m n c
      (integerTranslation ((N : ℤ) * l) * M * integerTranslation ((N : ℤ) * k)) =
      cuspGeometricPhase N m n c M := by
  obtain ⟨hA,_hC,hD⟩ := integerTranslation_entries ((N : ℤ) * l) ((N : ℤ) * k) M
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have he :
      ((m : ℝ) * ((integerTranslation ((N : ℤ) * l) * M * integerTranslation ((N : ℤ) * k)) 1 1 : ℝ) +
        (n : ℝ) * ((integerTranslation ((N : ℤ) * l) * M * integerTranslation ((N : ℤ) * k)) 0 0 : ℝ)) /
          ((N : ℝ) * c) =
      ((m : ℝ) * (M 1 1 : ℝ) + (n : ℝ) * (M 0 0 : ℝ)) / ((N : ℝ) * c) +
        ((m * k + n * l : ℤ) : ℝ) := by
    rw [hA,hD,hM]
    push_cast
    field_simp [hN,hcR]
    ring
  unfold cuspGeometricPhase
  rw [he,atkinPhase_add,atkinPhase_int,mul_one]

theorem cuspGeometricPhase_eq_of_residues (N : ℕ) [NeZero N]
    (m n c : ℤ) (hc : c ≠ 0) (M R : SL(2, ℤ))
    (hM : M 1 0 = c) (hR : R 1 0 = c)
    (hA : Int.ModEq ((N : ℤ) * c) (M 0 0) (R 0 0))
    (hD : Int.ModEq ((N : ℤ) * c) (M 1 1) (R 1 1)) :
    cuspGeometricPhase N m n c R = cuspGeometricPhase N m n c M := by
  obtain ⟨l,k,rfl⟩ := (integerTranslation_period_double_coset_iff N hc M R hM hR).mp ⟨hA,hD⟩
  exact cuspGeometricPhase_period_translate N m n c hc M hM l k

def gamma0PeriodKloostermanSum (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℕ) [NeZero c] (m n : ℤ) : ℂ :=
  ∑ R : gamma0CuspReducedMatrix N r s c, cuspGeometricPhase N m n c R.val

theorem gamma0PeriodKloostermanSum_trivial_bound (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ) :
    ‖gamma0PeriodKloostermanSum N r s c m n‖ ≤
      Fintype.card (gamma0CuspReducedMatrix N r s c) := by
  unfold gamma0PeriodKloostermanSum
  calc
    _ ≤ ∑ R : gamma0CuspReducedMatrix N r s c, ‖cuspGeometricPhase N m n c R.val‖ := norm_sum_le _ _
    _ = _ := by simp only [cuspGeometricPhase_norm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end ArtinMatthews
