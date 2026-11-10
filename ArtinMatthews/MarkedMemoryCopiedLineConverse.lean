module

public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedMinorArcRawLinePartition
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

/-! The converse copied-line gate for genuinely distinct prime slots.
Repeated prime slots are deliberately excluded: separate line equalities
then supply only one prime divisor rather than its higher powers. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedMemoryPositionLine_prime_dvd_of_eq (p : Nat.Primes)
    (z v : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (hv : IsCoprime v.1 v.2)
    (he : markedPrimePositionLine (p : ℕ) z hz=markedPrimePositionLine (p : ℕ) v hv) :
    (p : ℤ) ∣ markedMinorIntegerDet z v :=
  markedMinorSamePrimeLine_dvd (p : ℕ) z v
    ((markedPrimePositionLine_eq_iff_same (p : ℕ) z v hz hv).mp he)

theorem markedMemoryCopiedProduct_dvd_of_lines
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads : ℕ}
    (copied : MarkedRawActive P pads)
    (hinj : Function.Injective (fun a : (_j : J) × Fin pads => (copied a.1 a.2).1))
    (z v : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (hv : IsCoprime v.1 v.2)
    (hl : ∀ j k,markedPrimePositionLine ((copied j k).1 : ℕ) z hz=
      markedPrimePositionLine ((copied j k).1 : ℕ) v hv) :
    (markedRawCopiedProduct copied : ℤ) ∣ markedMinorIntegerDet z v := by
  classical
  have hp : (∏ a : (_j : J) × Fin pads,((copied a.1 a.2).1 : ℤ)) ∣
      markedMinorIntegerDet z v := by
    apply Fintype.prod_dvd_of_coprime
    · intro a b hab
      have hne : ((copied a.1 a.2).1 : ℕ)≠((copied b.1 b.2).1 : ℕ) := by
        intro he
        exact hab (hinj (Subtype.ext he))
      have hc := (Nat.coprime_primes (copied a.1 a.2).1.2 (copied b.1 b.2).1.2).mpr hne
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      simpa only [Int.gcd_def,Int.natAbs_natCast] using hc.gcd_eq_one
    · intro a
      exact markedMemoryPositionLine_prime_dvd_of_eq _ z v hz hv (hl a.1 a.2)
  simpa only [markedRawCopiedProduct,Nat.cast_prod,Fintype.prod_sigma] using hp

end
end ArtinMatthews
