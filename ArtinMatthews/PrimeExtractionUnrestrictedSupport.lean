module

public import ArtinMatthews.PrimeExtractionPrimeRoughIdentity
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

/-! The original shifted cutoff has finite integer support inside any
fixed larger truncation parameter, for all sufficiently large x. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators

theorem markedExtractionWeight_support_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b T : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hbT : b < T) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, markedExtractionWeight e G Φ x n ≠ 0 →
      n ∈ Finset.Ioc 0 ⌊T*x⌋₊ := by
  have hTb : 0 < T-b := sub_pos.mpr hbT
  have hzero : Φ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (hsupp hh).1
  filter_upwards [eventually_ge_atTop (1/(T-b)), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro n hn
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    exact hn (by simp only [markedExtractionWeight, Nat.zero_sub, Nat.cast_zero, zero_div,
      hzero, Complex.ofReal_zero, zero_mul])
  have hcut : Φ (((n-1 : ℕ) : ℝ)/x) ≠ 0 := by
    intro hz
    exact hn (by simp only [markedExtractionWeight, hz, Complex.ofReal_zero, zero_mul])
  have hupper := (div_le_iff₀ hx0).mp (hsupp hcut).2
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one] at hupper
  have hslack : 1 ≤ (T-b)*x := by
    calc
      1 = (T-b)*(1/(T-b)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hTb.le
  exact Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, Nat.le_floor (by linarith)⟩

theorem markedExtractionWeight_tsum_eq_sum_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b T : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hbT : b < T)
    (c : ℝ → ℕ → ℂ) :
    ∀ᶠ x : ℝ in atTop,
      (∑' n : ℕ, markedExtractionWeight e G Φ x n * c x n) =
        ∑ n ∈ Finset.Ioc 0 ⌊T*x⌋₊, markedExtractionWeight e G Φ x n * c x n := by
  filter_upwards [markedExtractionWeight_support_eventually e G Φ ha hsupp hbT] with x hx
  apply tsum_eq_sum
  intro n hn
  have hz : markedExtractionWeight e G Φ x n = 0 := by
    by_contra hh
    exact hn (hx n hh)
  rw [hz, zero_mul]

def markedUnrestrictedRoughThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (γ x : ℝ) : ℂ := by
  classical
  exact ∑' n : ℕ, markedExtractionWeight e G Φ x n *
    (if MarkedRoughAbove (x^γ) n then idealThetaCoeff η n * χ n else 0)

def markedUnrestrictedPrimeThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, markedExtractionWeight e G Φ x n *
    (if n.Prime then idealThetaCoeff η n * χ n else 0)

theorem markedUnrestrictedThetaSum_eq_finite_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b T : ℝ} (γ : ℝ)
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hbT : b < T) :
    ∀ᶠ x : ℝ in atTop,
      markedUnrestrictedRoughThetaSum e η χ G Φ γ x = markedActualRoughThetaSum e η χ G Φ T γ x ∧
        markedUnrestrictedPrimeThetaSum e η χ G Φ x = markedActualPrimeThetaSum e η χ G Φ T x := by
  classical
  filter_upwards [markedExtractionWeight_tsum_eq_sum_eventually e G Φ ha hsupp hbT
      (fun x n => if MarkedRoughAbove (x^γ) n then idealThetaCoeff η n * χ n else 0),
    markedExtractionWeight_tsum_eq_sum_eventually e G Φ ha hsupp hbT
      (fun _ n => if n.Prime then idealThetaCoeff η n * χ n else 0)] with x hr hp
  constructor
  · simpa only [markedUnrestrictedRoughThetaSum, markedActualRoughThetaSum,
      roughPositiveUpTo, Finset.sum_filter, mul_ite, mul_zero] using hr
  · simpa only [markedUnrestrictedPrimeThetaSum, markedActualPrimeThetaSum,
      Finset.sum_filter, mul_ite, mul_zero] using hp

end ArtinMatthews
