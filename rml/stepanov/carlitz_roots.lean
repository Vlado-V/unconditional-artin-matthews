/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

module

/- Ported to Lean 4.35.0-rc3: deprecated theorem aliases renamed.
   Original: Charlie Dorsey, Weil Bounds Toolkit, commit
   0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68. Apache-2.0. -/

public import rml.carlitz.recurrence_package
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

/-!
# Carlitz spectral roots

Connects the two spectral roots of the Carlitz recurrence to the formulation in Harcos
(2015), equation (2).
-/

namespace RML.ExpSum.Stepanov

open RML.ExpSum.Carlitz

noncomputable def carlitzAlpha
    (p : ℕ) [Fact p.Prime] (t : ZMod p) : ℂ :=
  if ht : t = 0 then 0
  else Classical.choose (carlitz_spectral_roots_Kext p ht)

noncomputable def carlitzBeta
    (p : ℕ) [Fact p.Prime] (t : ZMod p) : ℂ :=
  if ht : t = 0 then 0
  else Classical.choose (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))

theorem carlitzAlpha_add_beta
    (p : ℕ) [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    carlitzAlpha p t + carlitzBeta p t = -Kext p 1 t := by
  simp only [carlitzAlpha, carlitzBeta, dite_eq_right ht]
  exact (Classical.choose_spec (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))).1

theorem carlitzAlpha_mul_beta
    (p : ℕ) [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    carlitzAlpha p t * carlitzBeta p t = (p : ℂ) := by
  simp only [carlitzAlpha, carlitzBeta, dite_eq_right ht]
  exact (Classical.choose_spec (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))).2.1

theorem Kext_eq_neg_root_power_sum
    (p : ℕ) [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0)
    (r : ℕ) :
    Kext p (r + 1) t =
      -(carlitzAlpha p t ^ (r + 1) +
        carlitzBeta p t ^ (r + 1)) := by
  simp only [carlitzAlpha, carlitzBeta, dite_eq_right ht]
  exact (Classical.choose_spec (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))).2.2 r

#print axioms carlitzAlpha_add_beta
#print axioms carlitzAlpha_mul_beta
#print axioms Kext_eq_neg_root_power_sum


theorem Kext_eq_neg_root_power_sum_pos
    (p n : ℕ) [Fact p.Prime] {t : ZMod p}
    (ht : t ≠ 0) (hn : n ≠ 0) :
    letI : NeZero n := ⟨hn⟩
    RML.ExpSum.Carlitz.Kext p n t =
      -(carlitzAlpha p t ^ n + carlitzBeta p t ^ n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa [Nat.succ_eq_add_one] using
    Kext_eq_neg_root_power_sum p ht r

#print axioms Kext_eq_neg_root_power_sum_pos

end RML.ExpSum.Stepanov
