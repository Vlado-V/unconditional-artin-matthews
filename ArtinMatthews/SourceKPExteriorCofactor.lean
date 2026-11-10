module

public import ArtinMatthews.SourceKPIntegralResiduePhase
public import ArtinMatthews.ReflectionGaussDirectedPairs
public import ArtinMatthews.SourceKPLocalUnitResidue
public import ArtinMatthews.SourceJacquetActualShell
public import ArtinMatthews.SourceKPSIntegerLocalResidue
public import ArtinMatthews.SourcePrimeExponentValuation
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

/-! The literal omitted-prime product becomes the unit part of an
allowed product generator in the completion. Its residue is the
same quotient value used in the actual Gauss CRT expansion. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => PrincipalIntegerRing (sourceHilbertSeed K S₀)
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "D" => SourcePrimeExponents K S₀
local notation "p₀" => sourceAllowedPrimeGenerator K hζ S₀ P
local notation "hp₀" => sourceAllowedPrimeGenerator_ideal K hζ S₀ P
local notation "pchar" => generatorResidueCharacter (sourceHilbertSeed K S₀) P.val P.property p₀ hp₀
  (reflectionPrimeCharacters K hζ S₀ P)

def sourceKPCompletedExponentUnit (e : D) : Lˣ :=
  Units.map (algebraMap K L).toMonoidHom (sourcePrimeExponentUnit K hζ S₀ e)

local notation "u₀" => sourceKPCompletedExponentUnit K hζ S₀ P

theorem sourceKPCompletedExponentUnit_val (e : D) :
    (u₀ e : L) = algebraMap K L (sourcePrimeExponentGenerator K hζ S₀ e : K) := by
  change algebraMap K L (sourcePrimeExponentUnit K hζ S₀ e : K) = _
  rw [sourcePrimeExponentUnit_val]

theorem sourceKPCompletedExponentUnit_factor (e : D) :
    u₀ e = π₀ ^ e P * u₀ (e.erase P) := by
  have hprod := Finsupp.mul_prod_erase' e P
    (fun (Q : SourceExteriorPrime K S₀) (n : ℕ) => sourceAllowedPrimeUnit K hζ S₀ Q ^ n) (fun _ => pow_zero _)
  have hπ : Units.map (algebraMap K L).toMonoidHom (sourceAllowedPrimeUnit K hζ S₀ P) = π₀ := rfl
  change u₀ e = _
  unfold sourceKPCompletedExponentUnit sourcePrimeExponentUnit
  rw [← hprod, map_mul, map_pow, hπ]

theorem sourceKPCompletedExponentUnit_erase_valuation (e : D) :
    ν₀ (u₀ (e.erase P) : L) = 1 := by
  rw [sourceKPCompletedExponentUnit_val]
  change Valued.v ((sourcePrimeExponentGenerator K hζ S₀ (e.erase P) : K) : L) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', sourcePrimeExponentGenerator_valuation,
    Finsupp.erase_same, Nat.cast_zero, neg_zero, WithZero.exp_zero]

theorem sourceKPCompletedExponentUnit_erase_character (e : D)
    (T : Finset (SourceExteriorPrime K S₀)) (hT : e.support ⊆ T) :
    reflectionPrimeCharacters K hζ S₀ P
      (sourceKPLocalUnitResidue K P.val (u₀ (e.erase P))
        (sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e)) =
      ∏ Q ∈ T.erase P, reflectionPrimeCrossCharacter K hζ S₀ P Q ^ e Q := by
  rw [sourceKPLocalUnitResidue_eq_sInteger K hζ S₀ P
    (sourcePrimeExponentGenerator K hζ S₀ (e.erase P)) _
    (sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e) (sourceKPCompletedExponentUnit_val K hζ S₀ P _)]
  let p : R := p₀
  let M : Ideal R := Ideal.span {p}
  let q := Ideal.Quotient.mk M
  let g (Q : SourceExteriorPrime K S₀) : R := sourceAllowedPrimeGenerator K hζ S₀ Q
  let χ : MulChar (R ⧸ M) ℂ := pchar
  change χ (q (∏ Q ∈ (e.erase P).support, g Q ^ (e.erase P) Q)) = _
  rw [map_prod q, map_prod χ, Finsupp.support_erase]
  simp_rw [map_pow q, map_pow χ]
  calc
    _ = ∏ Q ∈ e.support.erase P, reflectionPrimeCrossCharacter K hζ S₀ P Q ^ e Q := by
      apply Finset.prod_congr rfl
      intro Q hQ
      rw [Finsupp.erase_ne (Finset.mem_erase.mp hQ).1]
      rfl
    _ = _ := by
      apply Finset.prod_subset (Finset.erase_subset_erase _ hT)
      intro Q hQT hQe
      have hn : Q ∉ e.support := fun h => hQe (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hQT).1, h⟩)
      rw [Finsupp.notMem_support_iff.mp hn, pow_zero]

theorem sourceKPExteriorCrossCharacter_pow_six (Q : SourceExteriorPrime K S₀) (hPQ : P ≠ Q) :
    reflectionPrimeCrossCharacter K hζ S₀ P Q ^ (6 : ℕ) = 1 := by
  let : P.val.asIdeal.IsMaximal := P.val.isPrime.isMaximal P.val.ne_bot
  let : Field ((𝓞 K) ⧸ P.val.asIdeal) := Ideal.Quotient.field _
  let x : R := sourceAllowedPrimeGenerator K hζ S₀ Q
  have hv : P.val.valuation K (x : K) = 1 := by
    rw [sourceAllowedPrimeGenerator_valuation, ite_eq_right (Ne.symm hPQ)]
  have hx : x ∉ P.val.asIdeal.map (algebraMap (𝓞 K) R) := by
    intro hm
    have h := (principalInteger_power_mem_iff_valuation (sourceHilbertSeed K S₀) P.val P.property 1 x).mp
      (by simpa only [pow_one] using hm)
    rw [hv, Nat.cast_one] at h
    exact (not_le_of_gt (WithZero.exp_lt_one_iff.mpr (by decide))) h
  let p : R := p₀
  let z := Ideal.Quotient.mk (Ideal.span {p}) x
  have hz : z ≠ 0 := by
    intro he
    apply hx
    have hI : P.val.asIdeal.map (algebraMap (𝓞 K) R) = Ideal.span {p} := hp₀
    rw [hI]
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  let equiv := generatorResidueEquiv (sourceHilbertSeed K S₀) P.val P.property p hp₀
  let a := equiv z
  have ha : a ≠ 0 := (map_ne_zero_iff equiv equiv.injective).mpr hz
  let χ := reflectionPrimeCharacters K hζ S₀ P
  have hp : χ ^ (6 : ℕ) = 1 := by
    rw [← sourceJacquetActualCharacter_order K hζ S₀ P]
    exact pow_orderOf_eq_one χ
  change χ a ^ (6 : ℕ) = 1
  rw [← MulChar.pow_apply' χ (by decide : (6 : ℕ) ≠ 0), hp, MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)]

end
end ArtinMatthews
