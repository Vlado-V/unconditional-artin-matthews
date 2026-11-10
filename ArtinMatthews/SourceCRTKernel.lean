module

public import ArtinMatthews.QuotientUnitChanges
public import ArtinMatthews.SIntegerSourceSexticF
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

/-! The genuine finite source F factors into the exact congruence
kernels used for quotient-unit normalization. The actual standard CRT
component is retained, with no local phase premise. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceCRTProductPhase (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (Ψ : AddChar ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P (fun j => k j + t j)) ℂ)
    (i : ι) : AddChar ((PrincipalIntegerRing S₀) ⧸
      (primePowerIdeal S₀ (P i) (k i) * primePowerIdeal S₀ (P i) (t i))) ℂ :=
  pullAddChar (Ideal.quotEquivOfEq (primePowerIdeal_add S₀ (P i) (k i) (t i)).symm)
    (probeCRTAddCharComponent
      (fun j => (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P j) (k j + t j))
      (primeCRTEquiv S₀ P (fun j => k j + t j) hP) Ψ i)

theorem sourceCRTLocalSum_eq_kernel (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (Ψ : AddChar ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P (fun j => k j + t j)) ℂ)
    (A H : PrincipalIntegerRing S₀)
    (W : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) → ℂ)
    (V : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) → ℂ) (i : ι) :
    sourceCRTLocalSum S₀ P k t hP Ψ A H W V i =
      quotientCongruenceKernel (primePowerIdeal S₀ (P i) (k i))
        (primePowerIdeal S₀ (P i) (t i)) A H (sourceCRTProductPhase S₀ P k t hP Ψ i) (W i) (V i) := by
  unfold sourceCRTLocalSum quotientCongruenceKernel
  apply tsum_congr
  intro d
  apply tsum_congr
  intro v
  split_ifs
  · rw [sourceCRTProductPhase, pullAddChar_apply]
    erw [Ideal.quotEquivOfEq_mk]
  · rfl

def sourceSexticCRTPhase (P : ι → HeightOneSpectrum (𝓞 K)) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (k t : ι → ℕ) : AddChar ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P (fun j => k j + t j)) ℂ :=
  sourceCRTPhase S₀ P (fun j => k j + t j)
    ((∏ j, a j ^ k j) * (∏ j, a j ^ t j))
    (mul_ne_zero (generatorProduct_ne_zero S₀ P a ha k) (generatorProduct_ne_zero S₀ P a ha t))
    (sourceCRT_modulus_product S₀ P k t _ _
      (crtModulus_generator S₀ P k a ha) (crtModulus_generator S₀ P t a ha))

theorem sourceSexticFiniteF_kernel_factor
    (P : ι → HeightOneSpectrum (𝓞 K)) (hP : Pairwise fun i j => P i ≠ P j)
    (hS : ∀ i, P i ∉ principalizingSet S₀) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (χ : ∀ i, MulChar ((𝓞 K) ⧸ (P i).asIdeal) ℂ) (k t : ι → ℕ) (H : PrincipalIntegerRing S₀) :
    sourceFiniteF S₀ (∏ i, a i ^ k i) (∏ i, a i ^ t i) H
      (sourceSexticWeight S₀ P hS a ha χ k) (sourceSexticWeight S₀ P hS a ha χ t) =
      ∏ i, quotientCongruenceKernel (primePowerIdeal S₀ (P i) (k i))
        (primePowerIdeal S₀ (P i) (t i)) (∏ j, a j ^ t j) H
        (sourceCRTProductPhase S₀ P k t hP (sourceSexticCRTPhase S₀ P a ha k t) i)
        (sourceLocalPowerWeight S₀ (P i) (hS i) (a i) (ha i) (χ i) (k i))
        (sourceLocalPowerWeight S₀ (P i) (hS i) (a i) (ha i) (χ i) (t i)) := by
  rw [sourceSexticFiniteF_factor S₀ P hP hS a ha χ k t H]
  apply Finset.prod_congr rfl
  intro i _
  exact sourceCRTLocalSum_eq_kernel S₀ P k t hP (sourceSexticCRTPhase S₀ P a ha k t)
    _ H _ _ i

end
end ArtinMatthews.SourceCRTNormalization
