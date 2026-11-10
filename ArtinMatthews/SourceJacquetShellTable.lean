module

public import ArtinMatthews.SourceJacquetShellCharacters
public import ArtinMatthews.SourceJacquetShellIntegral
public import ArtinMatthews.SourceJacquetDeepFrequency
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The complete literal shell integral table of source appendix10.
Its cutoff comes from actual Haar cancellation, and its terminal
coefficient is the actual standard-phase Gauss sum. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open StandardAdelic QuadraticWeil
open scoped NumberField ValuativeRel Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)

theorem sourceJacquetFrequency_valuation (u : P.adicCompletion F)
    (hu : (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (j : ℤ) : (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (u ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hu, ← WithZero.exp_zsmul]
  congr 1
  simp

def sourceJacquetLocalShell (e l : ℕ) : ℂ :=
  sourceJacquetShellIntegral F P (sourceJacquetShellCharacter F P χ l)
    ((sourceGeneratorCompletionUnit F S₀ P a ha : P.adicCompletion F) ^ ((e : ℤ) - (l : ℤ)))

theorem sourceJacquetLocalShell_eq_literal (hχ : orderOf χ = 6) (e l : ℕ) :
    sourceJacquetLocalShell F P S₀ a ha χ e l =
      sourceJacquetShellIntegral F P (χ ^ (-(8 * (l : ℤ))))
        ((sourceGeneratorCompletionUnit F S₀ P a ha : P.adicCompletion F) ^ ((e : ℤ) - (l : ℤ))) := by
  rw [sourceJacquetLocalShell, sourceJacquetShellCharacter_eq_negative F P χ hχ l]

theorem sourceJacquetLocalShell_table (hP : P ∉ principalizingSet S₀)
    (hbad : P ∉ traceBadPlaces F) (hχ : orderOf χ = 6) (e l : ℕ) :
    sourceJacquetLocalShell F P S₀ a ha χ e l =
      if l ≤ e then
        if 3 ∣ l then 1 - (Ideal.absNorm P.asIdeal : ℂ)⁻¹ else 0
      else if l = e + 1 then
        if 3 ∣ l then -(Ideal.absNorm P.asIdeal : ℂ)⁻¹
        else residueSourceTau S₀ P hP a ha (sourceJacquetShellCharacter F P χ l) /
          (Ideal.absNorm P.asIdeal : ℂ)
      else 0 := by
  let u : P.adicCompletion F := sourceGeneratorCompletionUnit F S₀ P a ha
  have hu : (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ))) u =
      WithZero.exp (-1 : ℤ) := sourceGeneratorCompletionUnit_valuation F S₀ P hP a ha
  have hq : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  by_cases hle : l ≤ e
  · rw [ite_eq_left hle, sourceJacquetLocalShell,
      sourceJacquetShellIntegral_of_integral_frequency,
      sourceJacquetShellCharacter_sum F P χ hχ l]
    · split_ifs
      · rw [sub_div, div_self hq, one_div]
      · exact zero_div _
    · change (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ)))
          (u ^ ((e : ℤ) - (l : ℤ))) ≤ 1
      rw [sourceJacquetFrequency_valuation F P u hu, WithZero.exp_le_one_iff]
      omega
  · rw [ite_eq_right hle]
    by_cases hlast : l = e + 1
    · have he : ((e : ℤ) - (l : ℤ)) = -1 := by omega
      rw [ite_eq_left hlast, sourceJacquetLocalShell, he, zpow_neg_one,
        sourceJacquetShellIntegral_primeGenerator F P S₀ hP a ha hbad]
      split_ifs with hl
      · rw [sourceJacquetShellCharacter_tau_principal F P χ hχ l hl S₀ hP a ha hbad,
          neg_div, one_div]
      · rfl
    · rw [ite_eq_right hlast, sourceJacquetLocalShell]
      apply sourceJacquetShellIntegral_deep_frequency F P _ u _ hu _ hbad
      change WithZero.exp (2 : ℤ) ≤ (Valued.v : Valuation (P.adicCompletion F)
        (WithZero (Multiplicative ℤ))) (u ^ ((e : ℤ) - (l : ℤ)))
      rw [sourceJacquetFrequency_valuation F P u hu, WithZero.exp_le_exp]
      omega

end
end ArtinMatthews
