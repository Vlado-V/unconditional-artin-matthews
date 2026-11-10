module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.PrimeExtractionPrimeRoughIdentity
public import ArtinMatthews.PrimeExtractionRelevantMellin
public import ArtinMatthews.PrimeExtractionArithmeticEndpoint
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The checked cubic rough-to-prime reduction consumes exactly the
remaining finite family of relevant Mellin tests, at the source cutoff. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped BigOperators Asymptotics ContDiff

def CubicSieveExtractionBoxSaving {J : Type*} [Fintype J] (e : J → ℝ)
    (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Icc 1 3)
    (ε γ : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊,
    (fun x => markedExtractionRelevantMellin e η χ (giantMarkedCenteredCore ε) Φ
      zero_lt_one hs hΦ γ j (Real.log x) x) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-1 : ℝ))

theorem cubicSieve_rough_sub_prime_isLittleO {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε γ : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) (hγ : 0 < γ) (hγ₁ : γ < 1)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Icc 1 3)
    (hboxes : CubicSieveExtractionBoxSaving e η χ Φ hΦ hs ε γ) :
    (fun x => markedActualRoughThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 γ x -
      markedActualPrimeThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 x) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-1 : ℝ)) := by
  have hc := (giantMarkedCenteredCore_interface e
    (fun j => (he j).2.trans_lt (by norm_num)) hε hεq).mono (fun _ h => h.1)
  have hr := markedActualRoughThetaSum_sub_prime_mellin_reduction
    e (fun j => (he j).1) η χ (giantMarkedCenteredCore ε) zero_le_one hc
    Φ zero_lt_one (by norm_num) hγ hγ₁ hs hΦ 1
  have hm := Asymptotics.IsLittleO.fun_sum (s := Finset.Icc 2 ⌈2 / γ⌉₊)
    (fun j hj => hboxes j hj)
  apply (hr.add hm).congr' _ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro x
  dsimp only [Pi.add_apply]
  ring

end ArtinMatthews
