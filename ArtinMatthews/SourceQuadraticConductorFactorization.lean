module

public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.SourceReflectionExteriorRows
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

/-! The quadratic conductor is the literal exterior ideal times a
factor dividing one fixed S-supported Hensel ideal. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem sourceFullExponentIdeal_finiteModulus (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    sourceFullExponentIdeal F (integralIdealFiniteModulus I hI) = I := by
  let J := sourceFullExponentIdeal F (integralIdealFiniteModulus I hI)
  have hJ : J ≠ ⊥ := sourceFullExponentIdeal_ne_bot F _
  have hmod : integralIdealFiniteModulus J hJ = integralIdealFiniteModulus I hI :=
    ArtinRay.integralIdealFiniteModulus_sourceFullExponentIdeal _
  exact le_antisymm
    (ArtinRay.integralIdeal_le_of_finiteModulus_le hI hJ hmod.symm.le)
    (ArtinRay.integralIdeal_le_of_finiteModulus_le hJ hI hmod.le)

variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "S" => sourceHilbertSet F S₀

def sourceQuadraticWildExponents (e : E) : HeightOneSpectrum (𝓞 F) →₀ ℕ :=
  (integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
    (sourceQuadraticConductor_ne_bot F S₀ hζ e)).filter (fun P => P ∈ S)

def sourceQuadraticWildIdeal (e : E) : Ideal (𝓞 F) :=
  sourceFullExponentIdeal F (sourceQuadraticWildExponents F S₀ hζ e)

theorem sourceQuadraticConductor_exponent_decomposition (e : E) (he : ∀ P, e P ≤ 1) :
    integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e) =
      e.embDomain (sourceReflectionExteriorPrimeEmbedding F S₀) +
        sourceQuadraticWildExponents F S₀ hζ e := by
  ext P
  by_cases hP : P ∈ S
  · have hr : P ∉ Set.range (sourceReflectionExteriorPrimeEmbedding F S₀) := by
      rintro ⟨Q, rfl⟩
      exact Q.property hP
    rw [Finsupp.add_apply, Finsupp.embDomain_of_notMem_range _ _ _ hr,
      zero_add, sourceQuadraticWildExponents, Finsupp.filter_apply, ite_eq_left hP]
  · let Q : SourceExteriorPrime F S₀ := ⟨P, hP⟩
    have hp : sourceReflectionExteriorPrimeEmbedding F S₀ Q = P := rfl
    have hQ : sourceReflectionExteriorPrimeEmbedding F S₀ Q ∉ S := Q.property
    rw [Finsupp.add_apply, ← hp, Finsupp.embDomain_apply_self,
      sourceQuadraticWildExponents, Finsupp.filter_apply, ite_eq_right hQ, add_zero]
    exact sourceQuadraticConductor_exterior F S₀ hζ e he Q

theorem sourceQuadraticConductor_factorization (e : E) (he : ∀ P, e P ≤ 1) :
    sourceQuadraticConductor F S₀ hζ e =
      sourcePrimeExponentIdeal F S₀ e * sourceQuadraticWildIdeal F S₀ hζ e := by
  nth_rw 1 [← sourceFullExponentIdeal_finiteModulus F _
    (sourceQuadraticConductor_ne_bot F S₀ hζ e)]
  rw [sourceQuadraticConductor_exponent_decomposition F S₀ hζ e he,
    sourceFullExponentIdeal_add, sourceReflectionFullExteriorIdeal]
  rfl

theorem sourceQuadraticWildIdeal_ne_bot (e : E) :
    sourceQuadraticWildIdeal F S₀ hζ e ≠ ⊥ :=
  sourceFullExponentIdeal_ne_bot F _

theorem sourceQuadraticWildIdeal_dvd_fixed (e : E) :
    sourceQuadraticWildIdeal F S₀ hζ e ∣ sixthKummerFixedIdeal S := by
  have hsupport : (sourceQuadraticWildExponents F S₀ hζ e).support ⊆ S := by
    intro P hP
    by_contra hn
    have hne := Finsupp.mem_support_iff.mp hP
    apply hne
    simp only [sourceQuadraticWildExponents, Finsupp.filter_apply, ite_eq_right hn]
  change (sourceQuadraticWildExponents F S₀ hζ e).prod (fun P n => P.asIdeal ^ n) ∣ _
  rw [Finsupp.prod_of_support_subset _ hsupport _ (fun P _ => pow_zero P.asIdeal)]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  rw [sourceQuadraticWildExponents, Finsupp.filter_apply, ite_eq_left hP]
  exact sourceQuadraticConductor_wild_le F S₀ hζ e P

theorem sourceQuadraticWildIdeal_support (e : E) (P : HeightOneSpectrum (𝓞 F))
    (hP : P ∉ S) : ¬ P.asIdeal ∣ sourceQuadraticWildIdeal F S₀ hζ e := by
  rw [← integralIdealFiniteModulus_mem_support _ (sourceQuadraticWildIdeal_ne_bot F S₀ hζ e) P]
  change P ∉ (integralIdealFiniteModulus
    (sourceFullExponentIdeal F (sourceQuadraticWildExponents F S₀ hζ e))
    (sourceQuadraticWildIdeal_ne_bot F S₀ hζ e)).support
  rw [ArtinRay.integralIdealFiniteModulus_sourceFullExponentIdeal, Finsupp.mem_support_iff]
  rw [sourceQuadraticWildExponents, Finsupp.filter_apply, ite_eq_right hP]
  exact fun h => h rfl

theorem sourceQuadraticConductor_norm_le (e : E) (he : ∀ P, e P ≤ 1) :
    (sourceQuadraticConductor F S₀ hζ e).absNorm ≤
      (sixthKummerFixedIdeal S).absNorm * sourcePrimeExponentNorm F S₀ e := by
  have hd : (sourceQuadraticWildIdeal F S₀ hζ e).absNorm ∣ (sixthKummerFixedIdeal S).absNorm :=
    map_dvd Ideal.absNorm (sourceQuadraticWildIdeal_dvd_fixed F S₀ hζ e)
  have hn : (sourceQuadraticWildIdeal F S₀ hζ e).absNorm ≤ (sixthKummerFixedIdeal S).absNorm :=
    Nat.le_of_dvd (sixthKummerFixedIdeal_absNorm_pos S) hd
  rw [sourceQuadraticConductor_factorization F S₀ hζ e he, map_mul, sourcePrimeExponentIdeal_norm]
  calc
    _ ≤ sourcePrimeExponentNorm F S₀ e * (sixthKummerFixedIdeal S).absNorm :=
      Nat.mul_le_mul_left _ hn
    _ = _ := Nat.mul_comm _ _

end
end ArtinMatthews.SourceEulerAssembly
