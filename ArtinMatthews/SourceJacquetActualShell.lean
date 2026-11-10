module

public import ArtinMatthews.SourceJacquetShellTable
public import ArtinMatthews.SourceJacquetGaussPair
public import ArtinMatthews.ReflectionGaussPrefix
public import ArtinMatthews.ProbeIdealCyclotomicSource
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

/-! The manuscript shell table for the actual exterior prime generator
and cyclotomic sextic character. The positive Gauss phase in the
manuscript is identified with the standard negative residue phase by
a genuine finite reindexing. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open StandardAdelic QuadraticWeil AllowedGenerators VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀)

theorem sourceJacquetActualCharacter_order : orderOf (reflectionPrimeCharacters F hζ S₀ P) = 6 :=
  cyclotomicAngularResidueCharacter_order hζ P.val
    (source_exterior_six_not_mem F S₀ P.val P.property)

theorem sourceJacquetActualCharacter_minus_one : reflectionPrimeCharacters F hζ S₀ P (-1) = 1 :=
  probeIdealCharacter_minus_one_of_twelve hζ P.val _ (sourceJacquetActualCharacter_order F hζ S₀ P)

def sourceJacquetActualGauss (j : ℕ) : ℂ :=
  sourceJacquetGauss F P.val (sourceHilbertSeed F S₀) P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (reflectionPrimeCharacters F hζ S₀ P) j

def sourceJacquetActualPositivePhase : AddChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ :=
  (residueSourcePhase (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P))⁻¹

theorem sourceJacquetActualPositivePhase_mk (x : 𝓞 F) :
    sourceJacquetActualPositivePhase F hζ S₀ P (Ideal.Quotient.mk _ x) =
      localFiniteCharacter F P.val
        (algebraMap F (P.val.adicCompletion F) ((x : F) / (sourceAllowedPrimeGenerator F hζ S₀ P : F))) := by
  rw [sourceJacquetActualPositivePhase, AddChar.inv_apply']
  have hx := residueSourcePhase_mk (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) x
  erw [hx, AddChar.map_neg_eq_inv, inv_inv]

theorem sourceJacquetActualGauss_positive (j : ℕ) :
    sourceJacquetActualGauss F hζ S₀ P j =
      (∑' x : (𝓞 F) ⧸ P.val.asIdeal, (reflectionPrimeCharacters F hζ S₀ P ^ j) x *
        sourceJacquetActualPositivePhase F hζ S₀ P x) / (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) := by
  let R := (𝓞 F) ⧸ P.val.asIdeal
  let χ := reflectionPrimeCharacters F hζ S₀ P
  let φ := residueSourcePhase (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
  have hm : (χ ^ j) (-1 : R) = 1 := by
    change (χ ^ j) ((-1 : Rˣ) : R) = 1
    rw [MulChar.pow_apply_coe, Units.val_neg, Units.val_one]
    change χ (-1) ^ j = 1
    rw [sourceJacquetActualCharacter_minus_one F hζ S₀ P, one_pow]
  have hneg (x : R) : (χ ^ j) (-x) = (χ ^ j) x := by
    rw [← neg_one_mul x, map_mul, hm, one_mul]
  change (∑' x : R, (χ ^ j) x * φ x) / _ = (∑' x : R, (χ ^ j) x * φ⁻¹ x) / _
  congr 1
  conv_rhs => rw [← (Equiv.neg R).tsum_eq (fun x : R => (χ ^ j) x * φ⁻¹ x)]
  apply tsum_congr
  intro x
  change (χ ^ j) x * φ x = (χ ^ j) (-x) * φ⁻¹ (-x)
  rw [hneg, AddChar.inv_apply, neg_neg]

theorem sourceJacquetActualGauss_two_eq_gamma :
    sourceJacquetActualGauss F hζ S₀ P 2 = reflectionNormalizedPrimeGamma F hζ S₀ P := rfl

theorem sourceJacquetActualGauss_two_four
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) :
    sourceJacquetActualGauss F hζ S₀ P 2 * sourceJacquetActualGauss F hζ S₀ P 4 = 1 :=
  sourceJacquetGauss_two_four F P.val (sourceHilbertSeed F S₀) P.property _ _ _
    (fun hp => P.property (hS (Finset.mem_union_left _ hp))) (sourceJacquetActualCharacter_order F hζ S₀ P)

theorem sourceJacquetActualGauss_norm (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (j : ℕ) (hj : ¬ 6 ∣ j) : ‖sourceJacquetActualGauss F hζ S₀ P j‖ = 1 := by
  apply sourceJacquetGauss_norm F P.val (sourceHilbertSeed F S₀) P.property _ _ _
    (fun hp => P.property (hS (Finset.mem_union_left _ hp))) j
  intro h
  apply hj
  rw [← sourceJacquetActualCharacter_order F hζ S₀ P]
  exact orderOf_dvd_iff_pow_eq_one.mpr h

def sourceJacquetActualShell (e l : ℕ) : ℂ :=
  sourceJacquetLocalShell F P.val (sourceHilbertSeed F S₀)
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (reflectionPrimeCharacters F hζ S₀ P) e l

theorem sourceJacquetActualShell_table (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (e l : ℕ) :
    sourceJacquetActualShell F hζ S₀ P e l =
      if l ≤ e then
        if 3 ∣ l then 1 - (Ideal.absNorm P.val.asIdeal : ℂ)⁻¹ else 0
      else if l = e + 1 then
        if 3 ∣ l then -(Ideal.absNorm P.val.asIdeal : ℂ)⁻¹
        else sourceJacquetActualGauss F hζ S₀ P (4 * l) /
          (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ)
      else 0 := by
  unfold sourceJacquetActualShell
  erw [sourceJacquetLocalShell_table F P.val (sourceHilbertSeed F S₀)
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (reflectionPrimeCharacters F hζ S₀ P) P.property
    (fun hp => P.property (hS (Finset.mem_union_left _ hp)))
    (sourceJacquetActualCharacter_order F hζ S₀ P) e l]
  split_ifs
  · rfl
  · rfl
  · rfl
  · let τ := residueSourceTau (sourceHilbertSeed F S₀) P.val P.property
        (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
        (reflectionPrimeCharacters F hζ S₀ P ^ (4 * l))
    change τ / (Ideal.absNorm P.val.asIdeal : ℂ) =
      (τ / (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ)) /
        (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ)
    rw [div_div, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  · rfl

end
end ArtinMatthews
