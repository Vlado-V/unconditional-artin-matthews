module

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

/-! Allowed generators define a genuine multiplicative class modulo
sixth powers of actual S-units, independent of every generator choice. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open GlobalClassFieldTheory.ClassFieldAxiom
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

abbrev sixthSUnitPowers (S₀ : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  sUnitNthPowersInField (K := K) 6 (sourceHilbertSet K S₀)

theorem mem_sixthSUnitPowers_iff (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    a ∈ sixthSUnitPowers K S₀ ↔
      ∃ t : SUnitGroup (K := K) (sourceHilbertSet K S₀), a = (t : Kˣ) ^ 6 := by
  constructor
  · rintro ⟨u, ⟨t, ht⟩, hu⟩
    refine ⟨t, ?_⟩
    have h := congrArg (fun v : SUnitGroup (K := K) (sourceHilbertSet K S₀) => (v : Kˣ)) ht
    exact hu.symm.trans h.symm
  · rintro ⟨t, rfl⟩
    exact ⟨t ^ 6, ⟨t, rfl⟩, rfl⟩

abbrev generatorClassGroup (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :=
  Kˣ ⧸ sixthSUnitPowers K S₀

theorem allowed_generator_class_eq {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) (a : Kˣ)
    (ha : a ∈ allowedSubgroup K hζ S₀)
    (hI : toPrincipalIdeal (sourceRing K S₀) K a = I) :
    QuotientGroup.mk' (sixthSUnitPowers K S₀) a =
      QuotientGroup.mk' (sixthSUnitPowers K S₀) (generator K hζ S₀ I) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply (mem_sixthSUnitPowers_iff K S₀ _).mpr
  exact allowed_ratio_sixth K hζ S₀ a _ ha (generator_allowed K hζ S₀ I)
    (hI.trans (generator_principal K hζ S₀ I).symm)

def generatorClassMap {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    idealGroup K S₀ →* generatorClassGroup K S₀ where
  toFun I := QuotientGroup.mk' (sixthSUnitPowers K S₀) (generator K hζ S₀ I)
  map_one' := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (mem_sixthSUnitPowers_iff K S₀ _).mpr (generator_one_sixth K hζ S₀)
  map_mul' I J := by
    rw [← map_mul]
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact (mem_sixthSUnitPowers_iff K S₀ _).mpr (generator_mul_ratio_sixth K hζ S₀ I J)

@[simp] theorem generatorClassMap_apply {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    generatorClassMap K hζ S₀ I =
      QuotientGroup.mk' (sixthSUnitPowers K S₀) (generator K hζ S₀ I) := rfl

end
end ArtinMatthews.AllowedGenerators
