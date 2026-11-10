module

public import ArtinMatthews.AllowedGeneratorBase
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Literal extension from integral-number-ring fractional ideals to
the constructed principal S-integer ring, compatible with principal
field generators and with ordinary ideal extension. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

private theorem fractionFieldExtension_eq_id (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    (IsFractionRing.map (K := K) (L := K)
      (FaithfulSMul.algebraMap_injective (𝓞 K) (sourceRing K S₀))) = RingHom.id K := by
  apply IsLocalization.ringHom_ext (𝓞 K)⁰
  apply RingHom.ext
  intro x
  change IsFractionRing.map
    (FaithfulSMul.algebraMap_injective (𝓞 K) (sourceRing K S₀))
      (algebraMap (𝓞 K) K x) = algebraMap (𝓞 K) K x
  rw [IsFractionRing.map, IsLocalization.map_eq]
  exact IsScalarTower.algebraMap_apply (𝓞 K) (sourceRing K S₀) K x

def fractionalIdealExtension (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    FractionalIdeal (𝓞 K)⁰ K →+* FractionalIdeal (sourceRing K S₀)⁰ K :=
  FractionalIdeal.extendedHom K (sourceRing K S₀)

theorem fractionalIdealExtension_span (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : K) :
    fractionalIdealExtension K S₀ (spanSingleton (𝓞 K)⁰ a) =
      spanSingleton (sourceRing K S₀)⁰ a := by
  simpa only [fractionalIdealExtension, fractionFieldExtension_eq_id, RingHom.id_apply] using
    (extendedHom_spanSingleton (A := 𝓞 K) (K := K) K (sourceRing K S₀) a)

def extendedIdealGroup (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* idealGroup K S₀ :=
  Units.map (fractionalIdealExtension K S₀).toMonoidHom

theorem extendedIdealGroup_principal (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    extendedIdealGroup K S₀ (toPrincipalIdeal (𝓞 K) K a) =
      toPrincipalIdeal (sourceRing K S₀) K a := by
  apply Units.ext
  simp only [extendedIdealGroup, Units.coe_map, coe_toPrincipalIdeal]
  change fractionalIdealExtension K S₀ (spanSingleton (𝓞 K)⁰ (a : K)) = _
  exact fractionalIdealExtension_span K S₀ (a : K)

theorem extendedIdealGroup_integral (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰) :
    (extendedIdealGroup K S₀ (FractionalIdeal.mk0 K I) :
      FractionalIdeal (sourceRing K S₀)⁰ K) =
      (I.val.map (algebraMap (𝓞 K) (sourceRing K S₀)) :
        FractionalIdeal (sourceRing K S₀)⁰ K) :=
  extendedHom_coeIdeal_eq_map K (sourceRing K S₀) I.val

theorem extendedIdealGroup_exterior (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed K S₀))) :
    (extendedIdealGroup K S₀ (FractionalIdeal.mk0 K ⟨I.val, by
      exact mem_nonZeroDivisors_iff_ne_zero.mpr I.property.1⟩) :
      FractionalIdeal (sourceRing K S₀)⁰ K) =
      ((show Ideal (sourceRing K S₀) from
        (principalExteriorIdealEquiv (sourceHilbertSeed K S₀) I).val) :
        FractionalIdeal (sourceRing K S₀)⁰ K) :=
  extendedHom_coeIdeal_eq_map K (sourceRing K S₀) I.val

end
end ArtinMatthews.AllowedGenerators
