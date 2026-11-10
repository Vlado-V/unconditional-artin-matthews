module

public import ArtinMatthews.GiantSignedMemoryCoordinates
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

/-! The actual small-prime torus and pending residue counting fiber. -/
namespace ArtinMatthews
noncomputable section

abbrev GiantSignedResidueFiber {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) :=
  GiantTwoSidedFullResidue PS × GiantSignedResidues primes

def giantSignedResidueDiagonal {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) :
    ℤ →+ GiantSignedResidueFiber PS primes where
  toFun d := (fun _ => (d : ZMod _), fun _ _ => (d : ZMod _))
  map_zero' := by ext <;> simp
  map_add' d e := by ext <;> simp

theorem giantSignedResidueDiagonal_translate {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) (d : ℤ)
    (x : GiantSignedResidueFiber PS primes) :
    x + giantSignedResidueDiagonal PS primes d =
      (giantTwoSidedResidueTranslate d x.1, giantSignedResidueTranslate primes d x.2) := rfl

theorem giantSignedResidueDiagonal_nsmul {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) (d : ℤ) (D : ℕ) :
    D • giantSignedResidueDiagonal PS primes d =
      giantSignedResidueDiagonal PS primes ((D : ℤ) * d) := by
  rw [← map_nsmul]
  congr 1

instance giantSignedResidueFiber_fintype {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val] {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) : Fintype (GiantSignedResidueFiber PS primes) := by
  classical
  letI : ∀ p : ↥(markedPhysicalBandPrimes PS), Fintype (ZMod p.val) := fun p => by
    let : NeZero p.val := ‹∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val› p
    infer_instance
  change Fintype (GiantTwoSidedFullResidue PS × GiantSignedResidues primes)
  infer_instance

end
end ArtinMatthews
