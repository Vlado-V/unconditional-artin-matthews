module

public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.ArtinAbelianEulerLog
public import ArtinMatthews.KummerCyclotomicTowerAbelian
public import ArtinMatthews.KummerSplittingGaloisField
public import ArtinMatthews.ArtinAbelianGlobalEuler
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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

/-! Genuine global Artin Euler factorizations for the actual auxiliary
cyclotomic/Kummer tower, on Re(s)>1. -/
noncomputable section
namespace ArtinMatthews
open scoped NumberField IsMulCommutative BigOperators

variable (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]

local instance cyclotomicGlobalArtinCharactersFintype :
    Fintype (Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) := Fintype.ofFinite _
local instance kummerGlobalArtinCharactersFintype :
    Fintype (Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ) := Fintype.ofFinite _

/-- Global factorization over the actual cyclotomic field ℚ(ζ_(12q)). -/
theorem twelfthKummer_cyclotomic_globalArtinFactorization {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (twelfthKummerField q a) s =
      ∏ χ : Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ,
        AbelianLocal.abelianArtinEulerProduct (twelfthCyclotomicField q)
          (twelfthKummerField q a) χ s :=
  AbelianLocal.dedekindZeta_eq_prod_abelianArtinEulerProduct _ _ hs

/-- Global factorization over the actual original Kummer field. -/
theorem twelfthKummer_original_globalArtinFactorization {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (twelfthKummerField q a) s =
      ∏ χ : Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ,
        AbelianLocal.abelianArtinEulerProduct (primeKummerField q a)
          (twelfthKummerField q a) χ s :=
  AbelianLocal.dedekindZeta_eq_prod_abelianArtinEulerProduct _ _ hs

end ArtinMatthews
