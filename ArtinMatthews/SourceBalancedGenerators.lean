module

public import ArtinMatthews.SLocalRingBalancedCompact
public import ArtinMatthews.SIntegerNormIdentification
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

/-! Source02 balanced generators, normalized by the genuine exterior
ideal norm. The integral norm is the literal finite quotient cardinality;
its extension to fractional ideals is positive and multiplicative. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain SUnitGroup FractionalIdeal
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem source_balanced_fractional_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    ∃ a : Kˣ, toPrincipalIdeal (sourceRing K S₀) K a = I ∧
      a ∈ allowedSubgroup K hζ S₀ ∧
      Units.map (sLocalRingDiagonal K (sourceHilbertSet K S₀)).toMonoidHom a /
        sourceRingScaling K hζ (sourceHilbertSet K S₀) (idealSNorm K hζ S₀ I) ∈
          sourceBalancedCompactSet K (sourceHilbertSet K S₀) :=
  ⟨balancedGenerator K hζ S₀ I, balancedGenerator_principal K hζ S₀ I,
    balancedGenerator_allowed K hζ S₀ I, balancedGenerator_sourceRing_compact K hζ S₀ I⟩

theorem source_balanced_integral_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (sourceRing K S₀))⁰) :
    ∃ a : sourceRing K S₀, ∃ ha : a ≠ 0,
      I.val = Ideal.span {a} ∧
      Units.mk0 (a : K) (by exact Subtype.coe_injective.ne ha) ∈ allowedSubgroup K hζ S₀ ∧
      Units.map (sLocalRingDiagonal K (sourceHilbertSet K S₀)).toMonoidHom
          (Units.mk0 (a : K) (by exact Subtype.coe_injective.ne ha)) /
        sourceRingScaling K hζ (sourceHilbertSet K S₀)
          (Nat.card ((sourceRing K S₀) ⧸ I.val) : ℝ) ∈
            sourceBalancedCompactSet K (sourceHilbertSet K S₀) := by
  let g := balancedGenerator K hζ S₀ (FractionalIdeal.mk0 K I)
  have heq : spanSingleton (sourceRing K S₀)⁰ (g : K) =
      (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) := by
    have h := congrArg Units.val (balancedGenerator_principal K hζ S₀ (FractionalIdeal.mk0 K I))
    simpa only [coe_toPrincipalIdeal, coe_mk0] using h
  have hmem : (g : K) ∈ (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) :=
    heq ▸ mem_spanSingleton_self (sourceRing K S₀)⁰ (g : K)
  obtain ⟨a, haI, hag⟩ := (mem_coeIdeal (sourceRing K S₀)⁰).mp hmem
  have ha : a ≠ 0 := by
    intro he
    apply g.ne_zero
    rw [← hag, he, map_zero]
  have hunit : Units.mk0 (a : K) (by exact Subtype.coe_injective.ne ha) = g := Units.ext hag
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · apply FractionalIdeal.coeIdeal_injective (K := K)
    change (I.val : FractionalIdeal (sourceRing K S₀)⁰ K) =
      (Ideal.span {a} : FractionalIdeal (sourceRing K S₀)⁰ K)
    rw [coeIdeal_span_singleton, hag]
    exact heq.symm
  · rw [hunit]
    exact balancedGenerator_allowed K hζ S₀ (FractionalIdeal.mk0 K I)
  · rw [hunit, ← idealSNorm_integral_card K hζ S₀ I]
    exact balancedGenerator_sourceRing_compact K hζ S₀ (FractionalIdeal.mk0 K I)

theorem source_balanced_compact_set {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : Set (SLocalRing K (sourceHilbertSet K S₀))ˣ,
      IsCompact C ∧ (∀ y ∈ C, sLocalRingNorm K (sourceHilbertSet K S₀) y = 1) ∧
      ∀ I : idealGroup K S₀,
        Units.map (sLocalRingDiagonal K (sourceHilbertSet K S₀)).toMonoidHom
            (balancedGenerator K hζ S₀ I) /
          sourceRingScaling K hζ (sourceHilbertSet K S₀) (idealSNorm K hζ S₀ I) ∈ C :=
  ⟨sourceBalancedCompactSet K (sourceHilbertSet K S₀),
    sourceBalancedCompactSet_isCompact K _, fun _ hy => sourceBalancedCompactSet_norm K _ hy,
    balancedGenerator_sourceRing_compact K hζ S₀⟩

end
end ArtinMatthews.AllowedGenerators
