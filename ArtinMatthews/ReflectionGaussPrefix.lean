module

public import ArtinMatthews.ReflectionGaussDirectedPairs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.Basify
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

/-! Exact normalization and support extension of the actual squarefree
gamma2 factor. Absent primes contribute one, and the directed diagonal
is omitted explicitly; no zero value is turned into an unmasked zeroth
character power. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open SIntegerFourier StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def reflectionNormalizedPrimeGamma (P : SourceExteriorPrime F S₀) : ℂ :=
  residueSourceTau (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (reflectionPrimeCharacters F hζ S₀ P ^ 2) / (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ)

theorem reflectionSquarefreeNorm_support (c : ReflectionSquarefreeExponents F S₀) :
    sourcePrimeExponentNorm F S₀ c.val = ∏ P : c.val.support, Ideal.absNorm P.val.val.asIdeal := by
  unfold sourcePrimeExponentNorm Finsupp.prod
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro P _
  rw [reflectionSquarefreeExponent_support_one F S₀ c P]
  change Ideal.absNorm P.val.val.asIdeal ^ 1 = _
  exact pow_one _

theorem reflectionSquarefreeNorm_sqrt_support (c : ReflectionSquarefreeExponents F S₀) :
    Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) =
      ∏ P : c.val.support, Real.sqrt (Ideal.absNorm P.val.val.asIdeal : ℝ) := by
  rw [reflectionSquarefreeNorm_support, Nat.cast_prod, Real.sqrt_prod]
  intro P _
  exact Nat.cast_nonneg _

theorem reflectionGammaTwo_eq_normalized_support (c : ReflectionSquarefreeExponents F S₀) :
    reflectionGammaTwo F hζ S₀ c.val =
      reflectionGaussDirectedPairs F hζ S₀ c *
        ∏ P : c.val.support, reflectionNormalizedPrimeGamma F hζ S₀ P.val := by
  have hs : (Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) : ℂ) =
      ∏ P : c.val.support, (Real.sqrt (Ideal.absNorm P.val.val.asIdeal : ℝ) : ℂ) := by
    rw [reflectionSquarefreeNorm_sqrt_support, Complex.ofReal_prod]
  rw [reflectionGammaTwo_eq_directed, hs, mul_div_assoc]
  unfold reflectionGaussPrimeProduct reflectionNormalizedPrimeGamma
  rw [Finset.prod_div_distrib]

private theorem squarefree_prod_prefix (c : ReflectionSquarefreeExponents F S₀)
    (f : SourceExteriorPrime F S₀ → ℂ) (T : Finset (SourceExteriorPrime F S₀)) (hT : c.val.support ⊆ T) :
    (∏ P : c.val.support, f P.val) = ∏ P ∈ T, f P ^ c.val P := by
  rw [Finset.prod_coe_sort]
  calc
    _ = ∏ P ∈ c.val.support, f P ^ c.val P := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [reflectionSquarefreeExponent_support_one F S₀ c ⟨P, hP⟩, pow_one]
    _ = _ := Finset.prod_subset hT (fun P _ hP => by
      rw [Finsupp.notMem_support_iff.mp hP, pow_zero])

def reflectionGaussPairKernel (c : ReflectionSquarefreeExponents F S₀)
    (P Q : SourceExteriorPrime F S₀) : ℂ :=
  if P = Q then 1 else reflectionPrimeCrossCharacter F hζ S₀ P Q ^ (2 * c.val P * c.val Q)

theorem reflectionGaussDirectedPairs_support (c : ReflectionSquarefreeExponents F S₀) :
    reflectionGaussDirectedPairs F hζ S₀ c =
      ∏ P ∈ c.val.support, ∏ Q ∈ c.val.support, reflectionGaussPairKernel F hζ S₀ c P Q := by
  unfold reflectionGaussDirectedPairs
  rw [← Finset.prod_coe_sort c.val.support
    (fun P => ∏ Q ∈ c.val.support, reflectionGaussPairKernel F hζ S₀ c P Q)]
  apply Finset.prod_congr rfl
  intro P _
  rw [← Finset.prod_coe_sort c.val.support (fun Q => reflectionGaussPairKernel F hζ S₀ c P.val Q)]
  calc
    _ = ∏ Q ∈ Finset.univ.erase P, reflectionGaussPairKernel F hζ S₀ c P.val Q.val := by
      apply Finset.prod_congr rfl
      intro Q hQ
      have hne : P.val ≠ Q.val := fun h => (Finset.mem_erase.mp hQ).1 (Subtype.ext h.symm)
      rw [reflectionGaussPairKernel, ite_eq_right hne,
        reflectionSquarefreeExponent_support_one F S₀ c P,
        reflectionSquarefreeExponent_support_one F S₀ c Q]
    _ = _ := Finset.prod_erase _ (by simp only [reflectionGaussPairKernel, ite_true])

theorem reflectionGaussDirectedPairs_prefix (c : ReflectionSquarefreeExponents F S₀)
    (T : Finset (SourceExteriorPrime F S₀)) (hT : c.val.support ⊆ T) :
    reflectionGaussDirectedPairs F hζ S₀ c =
      ∏ P ∈ T, ∏ Q ∈ T, reflectionGaussPairKernel F hζ S₀ c P Q := by
  rw [reflectionGaussDirectedPairs_support]
  calc
    _ = ∏ P ∈ c.val.support, ∏ Q ∈ T, reflectionGaussPairKernel F hζ S₀ c P Q := by
      apply Finset.prod_congr rfl
      intro P _
      apply Finset.prod_subset hT
      intro Q _ hQ
      simp only [reflectionGaussPairKernel, Finsupp.notMem_support_iff.mp hQ, mul_zero,
        pow_zero, ite_self]
    _ = _ := by
      apply Finset.prod_subset hT
      intro P _ hP
      apply Finset.prod_eq_one
      intro Q _
      simp only [reflectionGaussPairKernel, Finsupp.notMem_support_iff.mp hP, mul_zero,
        zero_mul, pow_zero, ite_self]

theorem reflectionGammaTwo_eq_prefix (c : ReflectionSquarefreeExponents F S₀)
    (T : Finset (SourceExteriorPrime F S₀)) (hT : c.val.support ⊆ T) :
    reflectionGammaTwo F hζ S₀ c.val =
      (∏ P ∈ T, ∏ Q ∈ T, reflectionGaussPairKernel F hζ S₀ c P Q) *
        ∏ P ∈ T, reflectionNormalizedPrimeGamma F hζ S₀ P ^ c.val P := by
  rw [reflectionGammaTwo_eq_normalized_support, reflectionGaussDirectedPairs_prefix F hζ S₀ c T hT,
    squarefree_prod_prefix F S₀ c (reflectionNormalizedPrimeGamma F hζ S₀) T hT]

end
end ArtinMatthews.VaryingKummerAnalytic
