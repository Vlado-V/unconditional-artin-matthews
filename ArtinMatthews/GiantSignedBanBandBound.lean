module

public import ArtinMatthews.GiantSignedAuxiliaryBan
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exclusion error is controlled by the actual harmonic atom and
the exact number of auxiliary-to-active comparisons. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedHarmonicAtom_upper (P : Finset ℕ) (p : P)
    (v Pmin : ℝ) (hv : 0 < v) (hPmin : 0 < Pmin)
    (hV : v ≤ bandReciprocalMass P) (hp : Pmin ≤ p.val) :
    markedHarmonicAtom P p ≤ 1 / (v * Pmin) := by
  have hp0 : 0 < (p.val : ℝ) := hPmin.trans_le hp
  unfold markedHarmonicAtom
  calc
    _ ≤ (1 / (p.val : ℝ)) / v :=
      div_le_div_of_nonneg_left (one_div_nonneg.mpr hp0.le) hv hV
    _ ≤ (1 / Pmin) / v :=
      div_le_div_of_nonneg_right (one_div_le_one_div_of_le hPmin hp) hv.le
    _ = _ := by ring

theorem giantSignedAuxiliaryBan_band_probability
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k M : ℕ}
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (v Pmin : ℝ) (hv : 0 < v) (hPmin : 0 < Pmin)
    (hV : ∀ j, v ≤ bandReciprocalMass (P j)) (hp : ∀ j (p : P j), Pmin ≤ p.val)
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
        (if GiantSignedAuxiliaryBan C a b aux then 0 else 1 : ℝ)) ≤
      ((∑ g, (C g).card) * (2 * M) : ℕ) / (v * Pmin) := by
  have h := giantSignedAuxiliaryBan_probability (fun j => hv.trans_le (hV j)) hdis C a b
    (1 / (v * Pmin)) (fun j p => giantSignedHarmonicAtom_upper (P j) p v Pmin hv hPmin (hV j) (hp j p))
  simpa only [div_eq_mul_inv, one_mul] using h

end
end ArtinMatthews
