module

public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedMajorLabelPolynomial
public import ArtinMatthews.RoughCharacterPrimes
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual unit support for the six-character major-arc expansion. The
centered coefficient is treated literally as prime minus normalized rough. -/
namespace ArtinMatthews
open Finset

theorem marked_centered_nonzero_coprime {q n : ℕ} [NeZero q]
    (W modulation : ℝ) (hq : (q:ℝ) ≤ W) (hn : W < (n:ℝ))
    (hcoeff : markedMajorCenteredCoefficient W modulation n ≠ 0) : n.Coprime q := by
  classical
  by_cases hp : n.Prime
  · exact Nat.coprime_of_lt_prime (NeZero.ne q) (by exact_mod_cast hq.trans_lt hn) hp
  · have hav : ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p∣n := by
      by_contra h
      simp [markedMajorCenteredCoefficient,hp,h] at hcoeff
    exact rough_avoid_coprime _ (rough_primesLE_covers_modulus W hq) hav

theorem marked_centered_nonzero_isUnit {q n : ℕ} [NeZero q]
    (W modulation : ℝ) (hq : (q:ℝ) ≤ W) (hn : W < (n:ℝ))
    (hcoeff : markedMajorCenteredCoefficient W modulation n ≠ 0) : IsUnit (n:ZMod q) :=
  (ZMod.isUnit_iff_coprime n q).mpr (marked_centered_nonzero_coprime W modulation hq hn hcoeff)

theorem marked_label_coprime {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    {q : ℕ} [NeZero q] (hq : ∀ j p,p ∈ bands j → q < p)
    {s : ℕ} (hs : s ∈ markedMajorLabelSet bands) : s.Coprime q := by
  classical
  obtain ⟨t,_,rfl⟩ := mem_image.mp hs
  unfold markedPrimeBandProduct
  exact Nat.coprime_prod_left_iff.mpr (fun j _ =>
    Nat.coprime_of_lt_prime (NeZero.ne q) (hq j _ (t j).property) (hbands j _ (t j).property))

theorem marked_label_isUnit {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    {q : ℕ} [NeZero q] (hq : ∀ j p,p ∈ bands j → q < p)
    {s : ℕ} (hs : s ∈ markedMajorLabelSet bands) : IsUnit (s:ZMod q) :=
  (ZMod.isUnit_iff_coprime s q).mpr (marked_label_coprime bands hbands hq hs)

theorem marked_rough_isUnit {q n : ℕ} [NeZero q]
    (W : ℝ) (hq : (q:ℝ) ≤ W)
    (hn : ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p∣n) : IsUnit (n:ZMod q) :=
  (ZMod.isUnit_iff_coprime n q).mpr (rough_avoid_coprime _ (rough_primesLE_covers_modulus W hq) hn)

end ArtinMatthews
