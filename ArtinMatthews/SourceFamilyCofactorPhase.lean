module

public import ArtinMatthews.SourceProductCofactorPhase
public import ArtinMatthews.SourceCofactorLocalOrder
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

/-! The inverse CRT cofactor is exactly the product of the source's
omitted s and A factors, inverted in the actual local quotient. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourceProductInverseCofactor_eq (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) (i : ι) :
    sourceProductInverseCofactor S₀ P hP a ha k t i =
      (sourceProductUnit S₀ (P i) (hS i) (a i) (ha i) (k i) (t i) (sourcePrimeCofactor S₀ a k i)
          (sourcePrimeCofactor_not_mem S₀ P hP hS a ha k i) *
        sourceProductUnit S₀ (P i) (hS i) (a i) (ha i) (k i) (t i) (sourcePrimeCofactor S₀ a t i)
          (sourcePrimeCofactor_not_mem S₀ P hP hS a ha t i))⁻¹ := by
  apply inv_injective
  rw [inv_inv]
  unfold sourceProductInverseCofactor
  rw [map_inv, inv_inv]
  apply Units.ext
  change (Ideal.quotEquivOfEq (primePowerIdeal_add S₀ (P i) (k i) (t i)))
      (sourcePrimeCofactorUnit S₀ P hP a ha (fun j => k j + t j) i :
        (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i + t i)) = _
  rw [sourcePrimeCofactorUnit_val, Ideal.quotEquivOfEq_mk, sourcePrimeCofactor_add,
    Units.val_mul, sourceProductUnit_val, sourceProductUnit_val, map_mul]

theorem sourceCRTProductPhase_eq_scaled (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) (i : ι) :
    sourceCRTProductPhase S₀ P k t hP (sourceSexticCRTPhase S₀ P a ha k t) i =
      (sourceLocalProductPhase S₀ (P i) (a i) (ha i) (k i) (t i)).mulShift
        ((sourceProductUnit S₀ (P i) (hS i) (a i) (ha i) (k i) (t i) (sourcePrimeCofactor S₀ a k i)
            (sourcePrimeCofactor_not_mem S₀ P hP hS a ha k i) *
          sourceProductUnit S₀ (P i) (hS i) (a i) (ha i) (k i) (t i) (sourcePrimeCofactor S₀ a t i)
            (sourcePrimeCofactor_not_mem S₀ P hP hS a ha t i))⁻¹ :
          ((PrincipalIntegerRing S₀) ⧸ (primePowerIdeal S₀ (P i) (k i) * primePowerIdeal S₀ (P i) (t i)))ˣ) := by
  rw [sourceCRTProductPhase_eq_inverseShift, sourceProductInverseCofactor_eq S₀ P hP hS a ha k t i]

end
end ArtinMatthews.SourceCRTNormalization
