module

public import ArtinMatthews.SourceLocalNormalizedCoefficient
public import ArtinMatthews.SourceUnitWeightValues
public import ArtinMatthews.SourceProductWeightHom
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

/-! The explicit directed source CRT factor. In complex units its value
is chi(hp)^(k-t) chi(sp)^t chi(ap)^(t-k), including degree zero. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceLocalUnitFactor_value (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t : ℕ) (sp ap hp : PrincipalIntegerRing S₀)
    (hsp : sp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hap : ap ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hhp : hp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceLocalUnitFactor S₀ P hP a ha χ k t sp ap hp hsp hap hhp =
      ((sourceCharacterUnit S₀ P hP a ha χ hp hhp ^ ((k : ℤ) - (t : ℤ)) *
        sourceCharacterUnit S₀ P hP a ha χ sp hsp ^ t *
        sourceCharacterUnit S₀ P hP a ha χ ap hap ^ ((t : ℤ) - (k : ℤ)) : ℂˣ) : ℂ) := by
  let s := sourceProductUnit S₀ P hP a ha k t sp hsp
  let b := sourceProductUnit S₀ P hP a ha k t ap hap
  let c := sourceProductUnit S₀ P hP a ha k t hp hhp
  let L := sourceProductWeightLeft S₀ P hP a ha χ k t
  let R := sourceProductWeightRight S₀ P hP a ha χ k t
  let α := sourceCharacterUnit S₀ P hP a ha χ sp hsp
  let β := sourceCharacterUnit S₀ P hP a ha χ ap hap
  let γ := sourceCharacterUnit S₀ P hP a ha χ hp hhp
  have hLc : L c = γ ^ k := sourceProductWeightLeft_element S₀ P hP a ha χ k t hp hhp
  have hLb : L b = β ^ k := sourceProductWeightLeft_element S₀ P hP a ha χ k t ap hap
  have hRs : R s = α ^ t := sourceProductWeightRight_element S₀ P hP a ha χ k t sp hsp
  have hRb : R b = β ^ t := sourceProductWeightRight_element S₀ P hP a ha χ k t ap hap
  have hRc : R c = γ ^ t := sourceProductWeightRight_element S₀ P hP a ha χ k t hp hhp
  have hu : L (c * b⁻¹) * R (s * b * c⁻¹) =
      (γ * β⁻¹) ^ k * (α * β * γ⁻¹) ^ t := by
    rw [map_mul L, map_inv L, map_mul R, map_mul R, map_inv R,
      hLc, hLb, hRs, hRb, hRc]
    simp only [mul_pow, inv_pow]
  have hz : (γ * β⁻¹) ^ k * (α * β * γ⁻¹) ^ t =
      γ ^ ((k : ℤ) - (t : ℤ)) * α ^ t * β ^ ((t : ℤ) - (k : ℤ)) := by
    simpa only [zpow_natCast] using sourceUnitFactor_zpow α β γ (k : ℤ) (t : ℤ)
  change (L (c * b⁻¹) : ℂ) * (R (s * b * c⁻¹) : ℂ) = _
  rw [← Units.val_mul, hu, hz]

end
end ArtinMatthews.SourceCRTNormalization
