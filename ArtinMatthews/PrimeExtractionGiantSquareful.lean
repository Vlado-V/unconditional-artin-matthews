module

public import ArtinMatthews.PrimeExtractionSquarefulWeighted
public import ArtinMatthews.GiantPrimeInvariance
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

/-! The exact giant-factor centered coefficient has negligible squareful
rough contribution; its global bounded-extension premise is discharged. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators Asymptotics

theorem markedSquarefulGiantThetaSum_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ : ℝ}
    (hT : 0 ≤ T) (hT2 : T ≤ 2) (hγ : 0 < γ) (A : ℝ) :
    markedSquarefulThetaSum e η χ
      (fun x u => (((giantPrimeFactors u x ε).card - giantPrimeReciprocalSum x ε : ℝ) : ℂ))
      Φ T γ =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  classical
  have hcore : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ,
      ‖((boundedGiantIndicator u x ε - giantPrimeReciprocalSum x ε : ℝ) : ℂ)‖ ≤ 1 := by
    filter_upwards [giantPrimeReciprocalSum_bounds_eventually hε hεq] with x hx
    intro u
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      boundedGiantIndicator_sub_abs_le_one u x ε _ hx.1 hx.2
  have h := markedSquarefulThetaSum_isLittleO e he η χ
    (fun x u => ((boundedGiantIndicator u x ε - giantPrimeReciprocalSum x ε : ℝ) : ℂ))
    (by norm_num : (0 : ℝ) ≤ 1) hcore Φ hΦ hT hγ A
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  unfold markedSquarefulThetaSum
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hnrange, hn0, _, hnsq⟩ := Finset.mem_filter.mp hn
  have hn1 : n ≠ 1 := by
    intro h
    exact hnsq (h ▸ squarefree_one)
  have hnT : (n : ℝ) ≤ T * x :=
    (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hnrange))).trans
      (Nat.floor_le (mul_nonneg hT (by linarith)))
  have hun : 0 < n - 1 := by omega
  have hux : ((n - 1 : ℕ) : ℝ) ≤ 2 * x :=
    (Nat.cast_le.mpr (Nat.sub_le n 1)).trans
      (hnT.trans (mul_le_mul_of_nonneg_right hT2 (by linarith)))
  dsimp only
  rw [boundedGiantIndicator_eq_card hun hux hx hεq.le]

end ArtinMatthews
