module

public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.StandardTameFiniteWeil
public import ArtinMatthews.SourceGeneratorPrefix
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceProductPhasePrimitive
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open StandardAdelic QuadraticWeil SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
local notation "R" => sourceRing F S₀
local notation "T" => sourceHilbertSeed F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀

include hBad in
theorem sourcePoissonExponentPhase_primitive (e : SourcePrimeExponents F S₀) (b : R)
    (hb : b ≠ 0) (hbe : b = a e) :
    (sIntegerQuotientPhase F S b hb).IsPrimitive := by
  let I := e.support
  let P (i : I) := i.val.val
  let A (i : I) := sourceAllowedPrimeGenerator F hζ S₀ i.val
  have hP : Pairwise fun i j => P i ≠ P j := by
    intro i j hij h
    exact hij (Subtype.ext (Subtype.ext h))
  have hS (i : I) : P i ∉ principalizingSet T := i.val.property
  have hA (i : I) :
      (P i).asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)) = Ideal.span {A i} :=
    sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val
  have htrace (i : I) : P i ∉ traceBadPlaces F := fun h =>
    hS i (hBad (Finset.mem_union_left _ h))
  have hEq : b = ∏ i : I, A i ^ e i.val :=
    hbe.trans (sourcePrimeExponentGenerator_prefix F hζ S₀ e I le_rfl)
  clear hbe
  subst b
  exact sourceProductQuotientPhase_primitive T P hP hS A hA (fun i => e i.val) htrace

include hBad in
theorem sourcePoissonProductPhase_primitive (s A : SourcePrimeExponents F S₀) :
    (sIntegerQuotientPhase F S (a s * a A)
      (mul_ne_zero (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s)
        (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A))).IsPrimitive :=
  sourcePoissonExponentPhase_primitive F S₀ hζ hBad (s + A) _
    (mul_ne_zero (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s)
      (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A))
    (sourcePrimeExponentGenerator_add F hζ S₀ s A).symm

end
end ArtinMatthews.SourceEulerAssembly
