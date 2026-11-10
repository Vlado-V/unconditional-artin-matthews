module

public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourcePrimeExponentValuation
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal omitted-prime cofactor of a fixed generator product. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourcePrimeExponentGenerator_single (P : SourceExteriorPrime F S₀) (n : ℕ) :
    sourcePrimeExponentGenerator F hζ S₀ (Finsupp.single P n) =
      sourceAllowedPrimeGenerator F hζ S₀ P ^ n :=
  Finsupp.prod_single_index
    (h := fun Q : SourceExteriorPrime F S₀ => fun k : ℕ => sourceAllowedPrimeGenerator F hζ S₀ Q ^ k)
    (a := P) (b := n) (pow_zero _)

theorem sourceExponent_single_add_erase (e : SourcePrimeExponents F S₀)
    (P : SourceExteriorPrime F S₀) : Finsupp.single P (e P) + e.erase P = e := by
  ext Q
  by_cases h : Q = P
  · subst Q
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.erase_same, add_zero]
  · simp only [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Ne.symm h),
      Finsupp.erase_ne h, zero_add]

def sourceGeneratorCofactor (e : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    sourceRing F S₀ := sourcePrimeExponentGenerator F hζ S₀ (e.erase P)

theorem sourceGeneratorCofactor_factor (e : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    sourcePrimeExponentGenerator F hζ S₀ e =
      sourceAllowedPrimeGenerator F hζ S₀ P ^ e P * sourceGeneratorCofactor F hζ S₀ e P := by
  unfold sourceGeneratorCofactor
  rw [← sourcePrimeExponentGenerator_single F hζ S₀ P (e P),
    ← sourcePrimeExponentGenerator_add, sourceExponent_single_add_erase]

theorem sourceGeneratorCofactor_not_mem (e : SourcePrimeExponents F S₀)
    (P : SourceExteriorPrime F S₀) : sourceGeneratorCofactor F hζ S₀ e P ∉
      P.val.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) := by
  intro hm
  unfold sourceGeneratorCofactor at hm
  have h := (sourcePrimeExponentGenerator_mem_primePower_iff F hζ S₀ (e.erase P) P 1).mp
    (by simpa only [pow_one] using hm)
  rw [Finsupp.erase_same] at h
  exact Nat.not_succ_le_zero 0 h

end
end ArtinMatthews
