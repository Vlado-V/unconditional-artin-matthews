module

public import ArtinMatthews.QuadraticHeckeMainTermEuler
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerAlgebra
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

namespace ArtinMatthews
open NumberField Complex VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The finite ideal Möbius sum at exponent one is the literal coprime density. -/
theorem quadraticHeckeCoprimeDensity_eq_divisor_sum
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    quadraticHeckeCoprimeDensity F m =
      ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) / (Ideal.absNorm d : ℂ) := by
  let A : Ideal (𝓞 F) →*₀ ℂ :=
    (riemannZetaSummandHom (s := (1 : ℂ)) (by norm_num)).comp Ideal.absNorm
  have hA (d : Ideal (𝓞 F)) : A d = (Ideal.absNorm d : ℂ)⁻¹ := by
    change (Ideal.absNorm d : ℂ) ^ (-(1 : ℂ)) = _
    exact Complex.cpow_neg_one _
  have h := HeckeIdealMobius.prime_product_eq_moebius_sum F m hm A
  simpa only [quadraticHeckeCoprimeDensity, hA, div_eq_mul_inv] using h

/-- Rescaling by each divisor extracts exactly the normalized Euler density. -/
theorem quadraticHeckeCoprimeDensity_rescaled_sum
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (X : ℝ) (A : ℂ) :
    (∑ d ∈ HeckeIdealMobius.divisors F m,
      (moebius d : ℂ) * (A * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ))) =
        A * (X : ℂ) * quadraticHeckeCoprimeDensity F m := by
  rw [quadraticHeckeCoprimeDensity_eq_divisor_sum F m hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  push_cast
  ring

end
end ArtinMatthews
