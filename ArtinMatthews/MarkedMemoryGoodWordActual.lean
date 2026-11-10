module

public import ArtinMatthews.MarkedMemoryGoodBoundary
public import ArtinMatthews.MarkedMemoryGoodWordBudget
public import ArtinMatthews.MarkedMinorArcDirtyScalar
public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMemoryGoodWordBoundary
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual endpoint/interior damping schedule and unit physical
cutoff, specialized to the literal good chronological boundary word. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def markedMemoryWordVisitQ (q : ℝ) (n j : ℕ) : ℝ :=
  if j = 0 ∨ j = n then Real.sqrt q else q

theorem markedMemoryWordVisitQ_bounds {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (n j : ℕ) :
    0 ≤ markedMemoryWordVisitQ q n j ∧ markedMemoryWordVisitQ q n j ≤ Real.sqrt q := by
  have hs₀ := Real.sqrt_nonneg q
  have hs₁ : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq₀]
  have hqs : q ≤ Real.sqrt q := by nlinarith [Real.sq_sqrt hq₀]
  unfold markedMemoryWordVisitQ
  split_ifs
  · exact ⟨hs₀, le_rfl⟩
  · exact ⟨hq₀, hqs⟩

theorem markedMemoryGoodBoundary_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    (q G H c T A W : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdepth : 100*(5*G+36) < (Fintype.card J : ℝ))
    (hψnorm : ∀ t, ‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z₀ : Z),
      0 < d₀ → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      ∀ n : ℕ, 0 < n →
      ‖markedMemoryBoundaryPairing
        (pads := ⌊(Real.log x)^(1/100 : ℝ)⌋₊) (B := markedDirtyMemoryCutoff x)
        (markedRawActualPrimeAtom e q x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) hZ ψ η d₀ Y
        ((Real.log x)^(G+9)) (markedMemoryChosenRho q) (markedMemoryWordVisitQ q n)
        (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) n 0 z₀‖ ≤
        ((Real.log x)^(-G))^n := by
  filter_upwards [markedMemoryGoodBoundary_chosen_rho_log_saving e he hinj ψ η hη hηnorm
    q G H c T A W hq₀ hq₁ hG hH hc hT hA hW hdepth hψnorm hsupp] with x hx
  intro Z hZ r d₀ Y w z₀ hd₀ hYlo hYhi hw hτ hbox n hn
  exact hx Z hZ r d₀ Y w (fun _ _ => 1) (markedMemoryWordVisitQ q n) z₀
    hd₀ hYlo hYhi hw hτ hbox (by intro j s; norm_num)
    (fun _ _ _ _ _ => rfl) (markedMemoryWordVisitQ_bounds hq₀ hq₁.le n) n 0 hn

end ArtinMatthews
