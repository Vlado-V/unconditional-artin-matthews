module

public import ArtinMatthews.SixthKummerSharpModulus
public import ArtinMatthews.SourceRowIntegralNumerator
public import ArtinMatthews.SourcePrimeNormSummability
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

/-! The exact exterior radical support and actual sharp conductor norm
bound for a source row, in terms of its literal frequency norm. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (u : sourceRing F S₀) (hu : u ≠ 0)
local notation "S" => sourceHilbertSet F S₀
local notation "E" => sourceElementExponents F S₀ u hu
local notation "v" => sourceRowFieldUnit F S₀ u hu

def sourceExteriorPrimeEmbedding : SourceExteriorPrime F S₀ ↪ HeightOneSpectrum (𝓞 F) :=
  ⟨Subtype.val, Subtype.val_injective⟩

include hζ

theorem sourceRowRadicalPrimes_eq_support :
    sixthExteriorRadicalPrimes S v = (E).support.map (sourceExteriorPrimeEmbedding F S₀) := by
  ext Q
  rw [mem_sixthExteriorRadicalPrimes, Finset.mem_map]
  constructor
  · rintro ⟨hQ, hv⟩
    let P : SourceExteriorPrime F S₀ := ⟨Q, hQ⟩
    refine ⟨P, Finsupp.mem_support_iff.mpr ?_, rfl⟩
    exact fun hj => hv ((sourceRowFieldUnit_count_zero_iff F S₀ hζ u hu P).mpr hj)
  · rintro ⟨P, hP, rfl⟩
    refine ⟨P.property, fun hv => (Finsupp.mem_support_iff.mp hP) ?_⟩
    exact (sourceRowFieldUnit_count_zero_iff F S₀ hζ u hu P).mp hv

theorem sourceRowRadicalIdeal_dvd :
    sixthExteriorRadicalIdeal S v ∣ sourcePrimeExponentIdeal F S₀ E := by
  rw [sixthExteriorRadicalIdeal, sourceRowRadicalPrimes_eq_support F hζ S₀ u hu, Finset.prod_map]
  change (∏ P ∈ (E).support, P.val.asIdeal) ∣ ∏ P ∈ (E).support, P.val.asIdeal ^ (E P)
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun P hP => dvd_pow_self _ (Finsupp.mem_support_iff.mp hP))

theorem sourceRowKummerSharpIdeal_norm_le :
    Ideal.absNorm (sixthKummerSharpIdeal S v) ≤
      Ideal.absNorm (sixthKummerFixedIdeal S) * sourcePrimeExponentNorm F S₀ E := by
  have hd := map_dvd Ideal.absNorm (sourceRowRadicalIdeal_dvd F hζ S₀ u hu)
  rw [sourcePrimeExponentIdeal_norm] at hd
  rw [sixthKummerSharpIdeal_absNorm]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (sourcePrimeExponentNorm_pos F S₀ _) hd)

end
end ArtinMatthews.SourceEulerAssembly
