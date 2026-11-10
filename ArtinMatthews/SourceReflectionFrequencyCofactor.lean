module

public import ArtinMatthews.SourceReflectionTameMonomial
public import ArtinMatthews.SourceReflectionDirectedCofactor
public import ArtinMatthews.SourceFrequencyUnitTransversal
public import ArtinMatthews.SLocalHilbertAlternating
public import ArtinMatthews.SourceFrequencyUnitPart
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

/-! Literal unit parts of the reflected frequency at every exterior prime. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic AllowedGenerators StandardAdelic
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField Classical ValuativeRel
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "U" => exteriorUnitSubgroup S
local notation "Γ" => SourceExteriorUnitSixthPowers S
local notation "a" => sourcePrimeExponentUnit K hζ S₀

variable (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "V" => sourceReflectionTameValuationUnits K S₀ P
local notation "j₀" => Units.map (RingHom.toMonoidHom (algebraMap K L))
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "χ" => sourceReflectionTameUnitCharacter K hζ S₀ P
local notation "u₀" => sourceKPCompletedExponentUnit K hζ S₀ P
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "D" => sourceReflectionDirectedCofactor K S₀ hζ P

def sourceReflectionExteriorUnitCompletion (P : SourceExteriorPrime K S₀) :
    exteriorUnitSubgroup (sourceHilbertSet K S₀) →* sourceReflectionTameValuationUnits K S₀ P := by
  let j := Units.map (RingHom.toMonoidHom (algebraMap K (P.val.adicCompletion K)))
  have hj (x : exteriorUnitSubgroup (sourceHilbertSet K S₀)) :
      j x.val ∈ sourceReflectionTameValuationUnits K S₀ P := by
    change Valued.v (algebraMap K (P.val.adicCompletion K) (x.val : K)) = 1
    have hv : Valued.v (algebraMap K (P.val.adicCompletion K) (x.val : K)) =
        P.val.valuation K (x.val : K) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P.val (x.val : K)
    exact hv.trans ((sourceExteriorPrincipalValuation_eq_zero_iff K P.val x.val).mp
      (x.property P.val P.property))
  exact (j.comp (exteriorUnitSubgroup (sourceHilbertSet K S₀)).subtype).codRestrict
    (sourceReflectionTameValuationUnits K S₀ P) hj

local notation "unitComp" => sourceReflectionExteriorUnitCompletion K S₀ P

include P in
theorem sourceReflectionExteriorUnitCompletion_val (ε : U) :
    (unitComp ε).val = j₀ ε.val := rfl

include P in
theorem sourceReflectionExteriorUnitCompletion_sixth (γ : Γ) : χ (unitComp γ.val) = 1 := by
  obtain ⟨v, hv⟩ := sourceExteriorUnitSixthPower_exists_root S γ
  rw [hv, map_pow, map_pow, sourceReflectionTameUnitCharacter_pow_six]

def sourceReflectionExteriorSign : U := ⟨-1, by
  intro Q _
  apply (sourceExteriorPrincipalValuation_eq_zero_iff K Q (-1)).mpr
  rw [Units.val_neg, Units.val_one, Valuation.map_neg, map_one]⟩

include hζ in
theorem sourceReflectionExteriorSign_sixth :
    sourceReflectionExteriorSign K S₀ ∈ Γ := by
  obtain ⟨z, hz⟩ := neg_one_is_sixth_power_of_primitive_twelve K hζ
  have hunit : z ∈ U := by
    intro Q hQ
    have hs := (sourceReflectionExteriorSign K S₀).property Q hQ
    change exteriorPrincipalValuation Q (-1 : Kˣ) = 0 at hs
    rw [← hz, exteriorPrincipalValuation_pow] at hs
    omega
  exact ⟨⟨z, hunit⟩, Subtype.ext hz⟩

include P hζ in
theorem sourceReflectionExteriorUnitCompletion_sign :
    χ (unitComp (sourceReflectionExteriorSign K S₀)) = 1 := by
  exact sourceReflectionExteriorUnitCompletion_sixth K S₀ hζ P
    ⟨_, sourceReflectionExteriorSign_sixth K S₀ hζ⟩

def sourceReflectionOmittedPrimeUnit (hζ : IsPrimitiveRoot ζ 12)
    (P : SourceExteriorPrime K S₀) (e : SourcePrimeExponents K S₀) :
    sourceReflectionTameValuationUnits K S₀ P :=
  ⟨sourceKPCompletedExponentUnit K hζ S₀ P (e.erase P),
    sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e⟩

theorem sourceReflectionOmittedPrimeUnit_character (hζ : IsPrimitiveRoot ζ 12)
    (P : SourceExteriorPrime K S₀) (e : SourcePrimeExponents K S₀) :
    sourceReflectionTameUnitCharacter K hζ S₀ P (sourceReflectionOmittedPrimeUnit K S₀ hζ P e) =
      sourceReflectionDirectedCofactor K S₀ hζ P e := by
  apply Units.ext
  exact (sourceReflectionTameUnitCharacter_val K hζ S₀ P _).trans
    (sourceReflectionDirectedCofactor_eq_residue K S₀ hζ P e).symm
/-- The completion-normalized unit in `ε·a_m/a_b²`, with the same
cofactor convention at numerator and denominator. -/
def sourceReflectionFrequencyLocalUnit (hζ : IsPrimitiveRoot ζ 12)
    (P : Pr) (ε : U) (m b : E) : sourceReflectionTameValuationUnits K S₀ P :=
  sourceReflectionExteriorUnitCompletion K S₀ P ε *
    sourceReflectionOmittedPrimeUnit K S₀ hζ P m *
    sourceReflectionOmittedPrimeUnit K S₀ hζ P b ^ (-2 : ℤ)

private theorem div_pow_two_factor {G : Type} [CommGroup G] (p ε u v : G) (m b : ℕ) :
    ε * (p ^ m * u) / (p ^ b * v) ^ (2 : ℕ) =
      p ^ ((m : ℤ) - 2 * (b : ℤ)) * (ε * u * v ^ (-2 : ℤ)) := by
  have hp : (p ^ b) ^ (2 : ℕ) = p ^ (2 * (b : ℤ)) := by
    rw [← pow_mul, ← zpow_natCast]
    congr 1
    push_cast
    ring
  have hv : v ^ (-2 : ℤ) = (v ^ (2 : ℕ))⁻¹ := by
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
  rw [mul_pow, div_eq_mul_inv, mul_inv_rev, zpow_sub, hp, hv, zpow_natCast]
  first
  | simp only [mul_assoc, mul_left_comm, mul_comm] <;> done
  | ac_nf <;> exact congrArg (fun x : G => ε * (u * x)) (mul_left_comm _ _ _)

include P in
theorem sourceReflectionFrequencyLocalUnit_completion (ε : U) (m b : E) :
    j₀ (ε.val * a m / (a b) ^ 2) =
      π₀ ^ ((m P : ℤ) - 2 * (b P : ℤ)) *
        (sourceReflectionFrequencyLocalUnit K S₀ hζ P ε m b).val := by
  rw [map_div, map_mul, map_pow]
  change j₀ ε.val * u₀ m / u₀ b ^ 2 = _
  rw [sourceKPCompletedExponentUnit_factor K hζ S₀ P m,
    sourceKPCompletedExponentUnit_factor K hζ S₀ P b]
  change j₀ ε.val * (π₀ ^ m P * u₀ (m.erase P)) /
      (π₀ ^ b P * u₀ (b.erase P)) ^ 2 =
    π₀ ^ ((m P : ℤ) - 2 * (b P : ℤ)) *
      (j₀ ε.val * u₀ (m.erase P) * u₀ (b.erase P) ^ (-2 : ℤ))
  exact div_pow_two_factor π₀ (j₀ ε.val) (u₀ (m.erase P)) (u₀ (b.erase P)) (m P) (b P)

include P in
theorem sourceReflectionFrequencyLocalUnit_character (ε : U) (m b : E) :
    χ (sourceReflectionFrequencyLocalUnit K S₀ hζ P ε m b) =
      χ (unitComp ε) * D m * (D b) ^ (-2 : ℤ) := by
  simp only [sourceReflectionFrequencyLocalUnit, map_mul, map_zpow,
    sourceReflectionOmittedPrimeUnit_character]

include P in
theorem sourceReflectionFrequencyLocalUnit_character_signed (ε : U) (γ : Γ) (m b : E) :
    χ (sourceReflectionFrequencyLocalUnit K S₀ hζ P
      (sourceReflectionExteriorSign K S₀ * (γ.val * ε)) m b) =
      χ (unitComp ε) * D m * (D b) ^ (-2 : ℤ) := by
  rw [sourceReflectionFrequencyLocalUnit_character]
  simp only [map_mul, sourceReflectionExteriorUnitCompletion_sign,
    sourceReflectionExteriorUnitCompletion_sixth, one_mul]

include P in
theorem sourceReflectionFrequencyLocalUnit_character_orbit (ε : U) (γ : Γ) (m b : E) :
    χ (sourceReflectionFrequencyLocalUnit K S₀ hζ P (γ.val * ε) m b) =
      χ (unitComp ε) * D m * (D b) ^ (-2 : ℤ) := by
  rw [sourceReflectionFrequencyLocalUnit_character]
  simp only [map_mul, sourceReflectionExteriorUnitCompletion_sixth, one_mul]

include P in
/-- The signed argument used by the active rotated row. -/
theorem sourceReflectionFrequencyLocalUnit_completion_signed (ε : U) (γ : Γ) (m b : E) :
    j₀ (-(γ.val.val * ε.val * a m / (a b) ^ 2)) =
      π₀ ^ ((m P : ℤ) - 2 * (b P : ℤ)) *
        (sourceReflectionFrequencyLocalUnit K S₀ hζ P
          (sourceReflectionExteriorSign K S₀ * (γ.val * ε)) m b).val := by
  have hv : (sourceReflectionExteriorSign K S₀ * (γ.val * ε)).val * a m / (a b) ^ 2 =
      -(γ.val.val * ε.val * a m / (a b) ^ 2) := by
    change (-1) * (γ.val.val * ε.val) * a m / (a b) ^ 2 = _
    simp only [neg_mul, neg_div, one_mul]
  rw [← hv]
  exact sourceReflectionFrequencyLocalUnit_completion K S₀ hζ P _ m b

end
end ArtinMatthews.SourceEulerAssembly
