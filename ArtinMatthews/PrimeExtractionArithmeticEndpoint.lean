module

public import ArtinMatthews.PrimeExtractionPrimeRoughIdentity
public import ArtinMatthews.PrimeExtractionRelevantMellin
public import ArtinMatthews.PrimeExtractionMellinReduction
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

/-! Complete arithmetic and Mellin reduction of the actual prime-versus-
rough difference. Only the explicitly displayed marked bilinear sums
remain to be bounded by the analytic coefficient criterion. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators ContDiff Asymptotics

theorem markedActualRoughThetaSum_sub_prime_mellin_reduction
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) {a T γ : ℝ} (ha : 0 < a) (hT : 0 ≤ T) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ) (A : ℝ) :
    (fun x => markedActualRoughThetaSum e η χ G Φ T γ x -
      markedActualPrimeThetaSum e η χ G Φ T x -
        ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
          markedExtractionRelevantMellin e η χ G Φ ha hsupp hΦ γ j (Real.log x) x) =o[atTop]
            (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  apply (markedActualCompositeThetaSum_relevant_mellin_reduction
    e he η χ G hCG hG Φ ha hT hγ hsupp hΦ A).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [markedActualRoughThetaSum_sub_prime_eq e η χ G Φ T ha hsupp hγ1] with x hx
  rw [hx]

end ArtinMatthews
