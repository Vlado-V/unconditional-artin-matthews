module

public import ArtinMatthews.AllowedGeneratorBase
public import ArtinMatthews.SIntegerExteriorIdealEquiv
public import ArtinMatthews.AllowedGeneratorSelection
public import ArtinMatthews.SIntegerPrincipalExterior
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

/-! Every genuine exterior integral ideal has an allowed generator in
the actual S-integer ring. No generator or principality premise is used. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem exists_integral_allowed_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (sourceRing K S₀))⁰) :
    ∃ a : sourceRing K S₀, ∃ ha : a ≠ 0,
      I.val = Ideal.span {a} ∧
      Units.mk0 (a : K) (by exact (Subtype.coe_injective.ne ha)) ∈ allowedSubgroup K hζ S₀ := by
  obtain ⟨a, ha, hB⟩ := exists_allowed_generator K hζ S₀ (FractionalIdeal.mk0 K I)
  have heq : spanSingleton (sourceRing K S₀)⁰ (a : K) =
      (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) := by
    have h := congrArg Units.val ha
    simpa only [coe_toPrincipalIdeal, coe_mk0] using h
  have hmem : (a : K) ∈ (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) :=
    heq ▸ mem_spanSingleton_self (sourceRing K S₀)⁰ (a : K)
  obtain ⟨b, hb, hba⟩ := (mem_coeIdeal (sourceRing K S₀)⁰).mp hmem
  have hb0 : b ≠ 0 := by
    intro he
    apply a.ne_zero
    rw [← hba, he, map_zero]
  refine ⟨b, hb0, ?_, ?_⟩
  · apply FractionalIdeal.coeIdeal_injective (K := K)
    change (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) =
      (Ideal.span {b} : FractionalIdeal (sourceRing K S₀)⁰ K)
    rw [coeIdeal_span_singleton, hba]
    exact heq.symm
  · have hunit : Units.mk0 (b : K) (by exact (Subtype.coe_injective.ne hb0)) = a :=
      Units.ext hba
    rw [hunit]
    exact hB

theorem exists_exterior_allowed_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed K S₀))) :
    ∃ a : sourceRing K S₀, ∃ ha : a ≠ 0,
      I.val.map (algebraMap (𝓞 K) (sourceRing K S₀)) = Ideal.span {a} ∧
      Units.mk0 (a : K) (by exact (Subtype.coe_injective.ne ha)) ∈ allowedSubgroup K hζ S₀ :=
  exists_integral_allowed_generator K hζ S₀
    (principalExteriorIdealEquiv (sourceHilbertSeed K S₀) I)

end
end ArtinMatthews.AllowedGenerators
