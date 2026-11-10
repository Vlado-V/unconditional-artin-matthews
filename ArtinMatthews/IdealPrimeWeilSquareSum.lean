module

public import ArtinMatthews.AdicIntegerResidueEquiv
public import ArtinMatthews.AdicPrimeResidueCharacter
public import ArtinMatthews.AnalyticWeilSquareClasses
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import ArtinMatthews.AdicPrimeQuadraticGaussian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Transport the literal arbitrary-prime quadratic Gaussian to the actual
number-field prime quotient, including the exact ideal norm denominator. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance idealWeilRelation : ValuativeRel (v.adicCompletion F) := adicRelation F v
local instance idealWeilLocalField : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
local instance idealWeilMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance idealWeilBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance idealWeilResidueFintype : Fintype 𝓀[v.adicCompletion F] := Fintype.ofFinite _
local instance idealWeilQuotientFinite : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
local instance idealWeilQuotientFintype : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _

variable (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : adicConductorZero F v ψ)
  (u : v.adicCompletion F)
  (hu : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))

def idealPrimeResidueChar : AddChar (𝓞 F ⧸ v.asIdeal) ℂ :=
  (adicPrimeResidueChar F v ψ hψ u hu).compAddMonoidHom (adicIntegerResidueEquiv F v).toAddMonoidHom

theorem idealPrimeResidueChar_mk (x : 𝓞 F) :
    idealPrimeResidueChar F v ψ hψ u hu (Ideal.Quotient.mk v.asIdeal x) =
      ψ (u⁻¹ * algebraMap (𝓞 F) (v.adicCompletion F) x) := by
  change adicPrimeResidueChar F v ψ hψ u hu
    (adicIntegerResidueEquiv F v (Ideal.Quotient.mk v.asIdeal x)) = _
  rw [adicIntegerResidueEquiv_mk, adicResidueOfInteger_apply, adicPrimeResidueChar_apply,
    adicIntegralOfInteger_val]

theorem idealPrimeResidueChar_nontrivial : idealPrimeResidueChar F v ψ hψ u hu ≠ 1 := by
  intro he
  apply adicPrimeResidueChar_nontrivial F v ψ hψ u hu
  ext z
  obtain ⟨x, rfl⟩ := (adicIntegerResidueEquiv F v).surjective z
  exact congrArg (fun χ : AddChar (𝓞 F ⧸ v.asIdeal) ℂ => χ x) he

theorem idealPrimeResidueChar_square_sum :
    (∑ x : 𝓞 F ⧸ v.asIdeal, idealPrimeResidueChar F v ψ hψ u hu (x ^ 2)) =
      ∑ z : 𝓀[v.adicCompletion F], adicPrimeResidueChar F v ψ hψ u hu (z ^ 2) := by
  calc
    _ = ∑ x : 𝓞 F ⧸ v.asIdeal,
        adicPrimeResidueChar F v ψ hψ u hu (adicIntegerResidueEquiv F v x ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (adicPrimeResidueChar F v ψ hψ u hu) (map_pow (adicIntegerResidueEquiv F v) x 2)
    _ = _ := (adicIntegerResidueEquiv F v).toEquiv.sum_comp
      (fun z : 𝓀[v.adicCompletion F] => adicPrimeResidueChar F v ψ hψ u hu (z ^ 2))

omit ψ hψ u hu in
theorem completedResidue_card_eq_norm : Fintype.card 𝓀[v.adicCompletion F] = Ideal.absNorm v.asIdeal := by
  have hc : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (adicIntegerResidueEquiv F v).toEquiv).symm.trans hc

theorem adicPrime_residueIndex_eq_idealSquareSum
    (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1) :
    residueIndex 𝓀[v.adicCompletion F] (adicPrimeResidueChar F v ψ hψ u hu) =
      (∑ x : 𝓞 F ⧸ v.asIdeal, idealPrimeResidueChar F v ψ hψ u hu (x ^ 2)) /
        (Real.sqrt (Ideal.absNorm v.asIdeal) : ℂ) := by
  rw [residueIndex_eq_square_sum
    (tameResidue_char_ne_two (v.adicCompletion F) (adic_canonical_two_unit F v h2))
    _ (adicPrimeResidueChar_nontrivial F v ψ hψ u hu),
    ← idealPrimeResidueChar_square_sum, completedResidue_card_eq_norm]

omit u hu in
theorem adicPrimeUnit_normalizedWeil_eq_idealSquareSum (a : (v.adicCompletion F)ˣ)
    (ha : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1) :
    analyticNormalizedWeil ψ a⁻¹ =
      (∑ x : 𝓞 F ⧸ v.asIdeal, idealPrimeResidueChar F v ψ hψ (a : v.adicCompletion F) ha (x ^ 2)) /
        (Real.sqrt (Ideal.absNorm v.asIdeal) : ℂ) := by
  have h := adicPrime_normalizedWeil_eq_residueIndex F v ψ hψ (a : v.adicCompletion F) ha hunit hc h2
  simp only [Units.mk0_val] at h
  exact h.trans (adicPrime_residueIndex_eq_idealSquareSum F v ψ hψ _ ha h2)

end

end ArtinMatthews.QuadraticWeil
