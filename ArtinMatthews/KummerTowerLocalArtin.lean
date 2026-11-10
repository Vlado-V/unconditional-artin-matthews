module

public import ArtinMatthews.ArtinAbelianLocalFactors
public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.KummerCyclotomicTowerAbelian
public import ArtinMatthews.KummerSplittingGaloisField
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! All-prime local Artin factorization for both actual abelian extensions
in the varying-q auxiliary tower. Ramified character factors are retained. -/

noncomputable section
namespace ArtinMatthews
open scoped NumberField IsMulCommutative BigOperators

variable (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]

local instance cyclotomicArtinCharactersFintype :
    Fintype (Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) := Fintype.ofFinite _
local instance kummerArtinCharactersFintype :
    Fintype (Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ) := Fintype.ofFinite _
local instance cyclotomicArtinPrimesFintype
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (twelfthCyclotomicField q))) :
    Fintype (Ideal.primesOver P.asIdeal (𝓞 (twelfthKummerField q a))) := Fintype.ofFinite _
local instance kummerArtinPrimesFintype
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (primeKummerField q a))) :
    Fintype (Ideal.primesOver P.asIdeal (𝓞 (twelfthKummerField q a))) := Fintype.ofFinite _

/-- Exact local factorization over F_q = ℚ(ζ_(12q)), at every actual prime. -/
theorem twelfthKummer_cyclotomic_localArtinFactorization
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (twelfthCyclotomicField q))) (s : ℂ) :
    (∏ χ : Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ,
      AbelianLocal.abelianArtinLocalFactor (twelfthCyclotomicField q) (twelfthKummerField q a)
        χ P s) =
      ∏ Q : Ideal.primesOver P.asIdeal (𝓞 (twelfthKummerField q a)),
        (1 - (Ideal.absNorm Q.val : ℂ) ^ (-s))⁻¹ :=
  AbelianLocal.prod_abelianArtinLocalFactor _ _ P s

/-- Exact local factorization over the original Kummer field, at every actual prime. -/
theorem twelfthKummer_original_localArtinFactorization
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (primeKummerField q a))) (s : ℂ) :
    (∏ χ : Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ,
      AbelianLocal.abelianArtinLocalFactor (primeKummerField q a) (twelfthKummerField q a)
        χ P s) =
      ∏ Q : Ideal.primesOver P.asIdeal (𝓞 (twelfthKummerField q a)),
        (1 - (Ideal.absNorm Q.val : ℂ) ^ (-s))⁻¹ :=
  AbelianLocal.prod_abelianArtinLocalFactor _ _ P s

end ArtinMatthews
