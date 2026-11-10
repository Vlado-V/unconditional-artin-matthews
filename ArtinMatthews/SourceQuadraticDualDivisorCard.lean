module

public import ArtinMatthews.SourceQuadraticRadicalRows
public import ArtinMatthews.QuadraticHeckeCoprimeContourRemainder
public import ArtinMatthews.QuadraticHeckeCutoffCoefficientBounds
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
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

theorem sourceQuadraticDual_outer_divisor_card (g : E) :
    (HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g)).card ≤
      Ideal.absNorm Bad * q g :=
  (quadraticHecke_divisor_card_le_norm F _ (sourceQuadraticBlockRadical_squarefree F S₀ g)).trans
    (sourceQuadraticBlockRadical_norm_le F S₀ g)

theorem sourceQuadraticDual_bad_divisor_card :
    (HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad)).card ≤ Ideal.absNorm Bad := by
  apply (quadraticHecke_divisor_card_le_norm F _ (quadraticHeckeIdealRadical_squarefree F Bad)).trans
  apply quadraticHeckeIdealRadical_norm_le F
  unfold sourceQuadraticBlockBadIdeal
  exact Ideal.span_singleton_eq_bot.not.mpr
    (SIntegerPrincipalization.principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))

theorem sourceQuadraticDual_divisor_norm_one_le (g : E) (d : Ideal (𝓞 F))
    (hd : d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g)) :
    1 ≤ (Ideal.absNorm d : ℝ) := by
  have hn := quadraticHeckeCoprime_divisor_norm_pos F (sourceQuadraticBlockRadical F S₀ g)
    (quadraticHeckeIdealRadical_ne_bot F _) hd
  exact_mod_cast (show 1 ≤ Ideal.absNorm d from Nat.succ_le_of_lt (by exact_mod_cast hn))

theorem sourceQuadraticDual_bad_norm_one_le (d : Ideal (𝓞 F))
    (hd : d ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad)) :
    1 ≤ (Ideal.absNorm d : ℝ) := by
  have hn := quadraticHeckeCoprime_divisor_norm_pos F (quadraticHeckeIdealRadical F Bad)
    (quadraticHeckeIdealRadical_ne_bot F _) hd
  exact_mod_cast (show 1 ≤ Ideal.absNorm d from Nat.succ_le_of_lt (by exact_mod_cast hn))

end
end ArtinMatthews.SourceEulerAssembly
