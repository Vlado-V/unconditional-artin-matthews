module

public import ArtinMatthews.AllowedGeneratorBase
public import ArtinMatthews.AllowedGeneratorSelection
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

/-! Sixth-power adjustments by actual S-units preserve both the ideal
and the one consistently selected allowed local class. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sUnit_sixth_globalClass (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) (sourceHilbertSet K S₀)) :
    sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) ((u : Kˣ) ^ 6) = 1 := by
  rw [map_pow]
  exact powerQuotient_pow_eq_one 6 _

theorem sUnit_sixth_allowed {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) (sourceHilbertSet K S₀)) :
    (u : Kˣ) ^ 6 ∈ allowedSubgroup K hζ S₀ := by
  change sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) ((u : Kˣ) ^ 6) ∈ chosenB K hζ S₀
  rw [sUnit_sixth_globalClass]
  exact (chosenB K hζ S₀).one_mem

theorem adjust_sixth_preserves_ideal (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ)
    (u : SUnitGroup (K := K) (sourceHilbertSet K S₀)) :
    toPrincipalIdeal (sourceRing K S₀) K (a * (u : Kˣ) ^ 6) =
      toPrincipalIdeal (sourceRing K S₀) K a := by
  rw [map_mul, map_pow, sUnit_principal_eq_one K S₀ u, one_pow, mul_one]

theorem adjust_sixth_preserves_allowed {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ)
    (ha : a ∈ allowedSubgroup K hζ S₀)
    (u : SUnitGroup (K := K) (sourceHilbertSet K S₀)) :
    a * (u : Kˣ) ^ 6 ∈ allowedSubgroup K hζ S₀ :=
  (allowedSubgroup K hζ S₀).mul_mem ha (sUnit_sixth_allowed K hζ S₀ u)

theorem allowed_same_ideal_iff_ratio_sixth {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ)
    (ha : a ∈ allowedSubgroup K hζ S₀) (hb : b ∈ allowedSubgroup K hζ S₀) :
    toPrincipalIdeal (sourceRing K S₀) K a = toPrincipalIdeal (sourceRing K S₀) K b ↔
      ∃ t : SUnitGroup (K := K) (sourceHilbertSet K S₀), a / b = (t : Kˣ) ^ 6 := by
  constructor
  · exact allowed_ratio_sixth K hζ S₀ a b ha hb
  · rintro ⟨t, ht⟩
    apply (principal_eq_iff_ratio_sUnit K S₀ a b).mpr
    rw [ht]
    exact (SUnitGroup (K := K) (sourceHilbertSet K S₀)).pow_mem t.property 6

end
end ArtinMatthews.AllowedGenerators
