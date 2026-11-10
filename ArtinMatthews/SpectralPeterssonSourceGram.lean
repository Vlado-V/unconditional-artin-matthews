module

public import ArtinMatthews.SpectralPeterssonWeightTwoGram
public import ArtinMatthews.SpectralMixedCuspInequivalent
public import ArtinMatthews.SpectralPeterssonWeightTwoAtkinGram
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source Gram on both same-sign sectors and every even
weight k ≥ 2. The weight-two vectors are the proved Abel limits. -/

noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

def gamma0PeterssonSourceInfinity (N : ℕ) [NeZero N] (k : ℕ) (n : ℕ+) : UpperHalfPlane → ℂ :=
  if k=2 then gamma0PeterssonWeightTwoInfinityNormalized N n else gamma0PeterssonNormalized N 1 k n

def gamma0PeterssonSourceAtkin (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (n : ℕ+) : UpperHalfPlane → ℂ :=
  if k=2 then gamma0PeterssonWeightTwoAtkinNormalized r s hab n
    else gamma0PeterssonNormalized (r*s) (gamma0CuspOneOver s) k n

def spectralPeterssonSignVector (negative : Bool) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  if negative then conj (F z) else F z

def gamma0PeterssonSignedGramModulusTerm (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (negative : Bool) (m n : ℕ+) (c : Ioi (0 : ℕ)) : ℂ :=
  if negative then gamma0PeterssonNegativeGramModulusTerm N b a k m n c
    else gamma0PeterssonGramModulusTerm N b a k m n c

private theorem peterssonSource_signed_of_positive (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hEven : Even k) (negative : Bool) (m n : ℕ+) (F G : UpperHalfPlane → ℂ) (d : ℝ)
    (h : Summable (gamma0PeterssonGramModulusTerm N b a k m n) ∧
      gamma0PeterssonInner N k F G = (d : ℂ)+∑' c, gamma0PeterssonGramModulusTerm N b a k m n c) :
    Summable (gamma0PeterssonSignedGramModulusTerm N b a k negative m n) ∧
      gamma0PeterssonInner N k (spectralPeterssonSignVector negative F) (spectralPeterssonSignVector negative G) =
        (d : ℂ)+∑' c, gamma0PeterssonSignedGramModulusTerm N b a k negative m n c := by
  cases negative
  · exact h
  · exact gamma0PeterssonInner_negative_of_positive N b a k hEven m n F G d h.1 h.2

theorem gamma0PeterssonSourceInfinity_signed_gram (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k)
    (hEven : Even k) (negative : Bool) (m n : ℕ+) :
    Summable (gamma0PeterssonSignedGramModulusTerm N 1 1 k negative m n) ∧
      gamma0PeterssonInner N k (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity N k n))
        (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity N k m)) =
        (if m=n then 1 else 0)+∑' c, gamma0PeterssonSignedGramModulusTerm N 1 1 k negative m n c := by
  have hd : (((if m=n then 1 else 0) : ℝ) : ℂ) = (if m=n then 1 else 0) := by split_ifs <;> simp
  rw [← hd]
  apply peterssonSource_signed_of_positive N 1 1 k hEven negative m n _ _
  rw [hd]
  by_cases he : k=2
  · subst k
    simpa [gamma0PeterssonSourceInfinity] using gamma0PeterssonWeightTwoInfinity_gram N m n
  · simpa only [gamma0PeterssonSourceInfinity,ite_eq_right he] using
      gamma0PeterssonNormalized_same_cusp_gram N 1 k (by omega) hEven m n

theorem gamma0PeterssonSourceAtkin_signed_gram (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k)
    (hEven : Even k) (negative : Bool) (m n : ℕ+) :
    Summable (gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) k negative m n) ∧
      gamma0PeterssonInner (r*s) k
        (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab k n))
        (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab k m)) =
        (if m=n then 1 else 0)+
          ∑' c, gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) k negative m n c := by
  have hd : (((if m=n then 1 else 0) : ℝ) : ℂ) = (if m=n then 1 else 0) := by split_ifs <;> simp
  rw [← hd]
  apply peterssonSource_signed_of_positive (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) k hEven negative m n _ _
  rw [hd]
  by_cases he : k=2
  · subst k
    simpa [gamma0PeterssonSourceAtkin] using gamma0PeterssonWeightTwoAtkin_gram r s hcop hab m n
  · simpa only [gamma0PeterssonSourceAtkin,ite_eq_right he] using
      gamma0PeterssonNormalized_same_cusp_gram (r*s) (gamma0CuspOneOver s) k (by omega) hEven m n

theorem gamma0PeterssonSourceMixed_signed_gram (r s : ℕ) [NeZero r] [NeZero s]
    (hr : 1 < r) (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k)
    (hEven : Even k) (negative : Bool) (m n : ℕ+) :
    Summable (gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 k negative m n) ∧
      gamma0PeterssonInner (r*s) k
        (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab k n))
        (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity (r*s) k m)) =
        ∑' c, gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 k negative m n c := by
  have h : Summable (gamma0PeterssonGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 k m n) ∧
      gamma0PeterssonInner (r*s) k (gamma0PeterssonSourceAtkin r s hab k n)
        (gamma0PeterssonSourceInfinity (r*s) k m) =
        ∑' c, gamma0PeterssonGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 k m n c := by
    by_cases he : k=2
    · subst k
      simpa [gamma0PeterssonSourceAtkin,gamma0PeterssonSourceInfinity] using
        gamma0PeterssonWeightTwoMixed_gram r s hr hcop hab m n
    · simpa only [gamma0PeterssonSourceAtkin,gamma0PeterssonSourceInfinity,ite_eq_right he] using
        gamma0PeterssonNormalized_inequivalent_gram (r*s) (gamma0CuspOneOver s) 1
          (gamma0MixedCusps_inequivalent_of_one_lt r s hr) k (by omega) hEven m n
  simpa only [Complex.ofReal_zero,zero_add] using peterssonSource_signed_of_positive (r*s) (gamma0CuspOneOver s) 1
    k hEven negative m n _ _ 0 (by simpa only [Complex.ofReal_zero,zero_add] using h)

end ArtinMatthews
