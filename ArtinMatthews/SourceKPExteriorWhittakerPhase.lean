module

public import ArtinMatthews.SourceKPExteriorCofactor
public import ArtinMatthews.SourceKPTameCyclicWhittakerValues
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exterior Whittaker phase for an allowed generator of c n³ is
the exact directed CRT row of the global quadratic Gauss factor. The
powers divisible by six disappear on actual unit residues. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "D" => SourcePrimeExponents K S₀
local notation "u₀" => sourceKPCompletedExponentUnit K hζ S₀ P
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P

variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS

def sourceKPTameExteriorWhittakerDiagonal (a : Kˣ) : ℂ :=
  W₀ (l₀ (sourceGL2Diagonal (Units.map (algebraMap K L).toMonoidHom a)))

theorem sourceKPTameExteriorWhittakerDiagonal_exponent (e : D) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (sourcePrimeExponentUnit K hζ S₀ e) =
      χ₀ (sourceKPLocalUnitResidue K P.val (u₀ (e.erase P))
        (sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e)) ^ (2 * (e P : ℤ)) *
        W₀ (l₀ (sourceGL2Diagonal (π₀ ^ (e P : ℤ)))) := by
  change W₀ (l₀ (sourceGL2Diagonal (u₀ e))) = _
  rw [sourceKPCompletedExponentUnit_factor K hζ S₀ P e, ← zpow_natCast]
  exact sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS (e P : ℤ)
    (u₀ (e.erase P)) (sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e)

theorem sourceKPTameExteriorWhittakerDiagonal_exponent_zero (e : D) (he : e P = 0) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (sourcePrimeExponentUnit K hζ S₀ e) = 1 := by
  rw [sourceKPTameExteriorWhittakerDiagonal_exponent, he, Nat.cast_zero, mul_zero, zpow_zero,
    zpow_zero, one_mul]
  have hdiag : sourceGL2Diagonal (1 : Lˣ) = 1 := (sourceGL2DiagonalHom L).map_one
  have hl : l₀ 1 = 1 := (sourceFiniteKP2ProjectiveMk K hζ P.val).map_one
  rw [hdiag, hl, sourceKPTameCyclicWhittakerValue_one]

theorem sourceKPExteriorWhittakerPhase_squarefree_cube (c : ReflectionSquarefreeExponents K S₀)
    (n : D) (T : Finset (SourceExteriorPrime K S₀)) (hT : (c.val + 3 • n).support ⊆ T) :
    let e := c.val + 3 • n
    χ₀ (sourceKPLocalUnitResidue K P.val (u₀ (e.erase P))
      (sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e)) ^ (2 * (e P : ℤ)) =
      ∏ Q ∈ T, reflectionGaussPairKernel K hζ S₀ c P Q := by
  let e := c.val + 3 • n
  change χ₀ (sourceKPLocalUnitResidue K P.val (u₀ (e.erase P))
    (sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e)) ^ (2 * (e P : ℤ)) = _
  rw [sourceKPCompletedExponentUnit_erase_character K hζ S₀ P e T hT,
    show 2 * (e P : ℤ) = ((2 * e P : ℕ) : ℤ) by norm_cast, zpow_natCast, ← Finset.prod_pow]
  calc
    _ = ∏ Q ∈ T.erase P, reflectionGaussPairKernel K hζ S₀ c P Q := by
      apply Finset.prod_congr rfl
      intro Q hQ
      have hPQ : P ≠ Q := (Finset.mem_erase.mp hQ).1.symm
      have hexp : e Q * (2 * e P) =
          2 * c.val P * c.val Q + 6 * (n P * c.val Q + c.val P * n Q + 3 * n P * n Q) := by
        simp only [e, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        ring
      have hp : reflectionPrimeCrossCharacter K hζ S₀ P Q ^
          (6 * (n P * c.val Q + c.val P * n Q + 3 * n P * n Q)) = 1 := by
        rw [pow_mul, sourceKPExteriorCrossCharacter_pow_six K hζ S₀ P Q hPQ, one_pow]
      rw [← pow_mul, hexp, pow_add, hp, mul_one]
      exact (ite_eq_right hPQ).symm
    _ = _ := Finset.prod_erase _ (by simp only [reflectionGaussPairKernel, ite_true])

end
end ArtinMatthews
