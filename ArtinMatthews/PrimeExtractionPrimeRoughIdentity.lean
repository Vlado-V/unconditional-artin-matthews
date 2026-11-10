module

public import ArtinMatthews.PrimeExtractionCompositeError
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite prime-minus-rough identity on the actual smooth
support. Its composite term is the one reduced to Mellin sums. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators

theorem prime_extraction_roughness_below_support {a γ : ℝ} (ha : 0 < a) (hγ : γ < 1) :
    ∀ᶠ x : ℝ in atTop, x^γ < a*x := by
  have ht := (tendsto_rpow_neg_atTop (by linarith : 0 < 1-γ)).eventually (gt_mem_nhds ha)
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have heq : x^γ = x^(-(1-γ))*x := by
    calc
      _ = x^(-(1-γ)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
  rw [heq]
  exact mul_lt_mul_of_pos_right hx hx0

theorem markedExtractionWeight_prime_rough_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b γ : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hγ : γ < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ p : ℕ, p.Prime →
      markedExtractionWeight e G Φ x p ≠ 0 → MarkedRoughAbove (x^γ) p := by
  filter_upwards [prime_extraction_roughness_below_support ha hγ,
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro p hp hw
  have hcut : Φ (((p-1 : ℕ) : ℝ)/x) ≠ 0 := by
    intro hz
    exact hw (by simp only [markedExtractionWeight, hz, Complex.ofReal_zero, zero_mul])
  have hlow := (le_div_iff₀ hx0).mp (hsupp hcut).1
  have hpred : ((p-1 : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hpgt : x^γ < (p : ℝ) := hx.trans_le (hlow.trans hpred)
  intro r hr hrd
  have hrp : r = p := ((Nat.dvd_prime hp).mp hrd).resolve_left hr.ne_one
  simpa only [hrp] using hpgt

def markedActualRoughThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ roughPositiveUpTo ⌊T*x⌋₊ (x^γ),
    markedExtractionWeight e G Φ x n * (idealThetaCoeff η n * χ n)

def markedActualPrimeThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊T*x⌋₊).filter Nat.Prime,
    markedExtractionWeight e G Φ x n * (idealThetaCoeff η n * χ n)

theorem markedActualRoughThetaSum_sub_prime_eq {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b γ : ℝ} (T : ℝ)
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hγ : γ < 1) :
    ∀ᶠ x : ℝ in atTop,
      markedActualRoughThetaSum e η χ G Φ T γ x - markedActualPrimeThetaSum e η χ G Φ T x =
        markedActualCompositeThetaSum e η χ G Φ T γ x := by
  classical
  have hzero : Φ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (hsupp hh).1
  filter_upwards [markedExtractionWeight_prime_rough_eventually e G Φ ha hsupp hγ] with x hx
  have hw1 : markedExtractionWeight e G Φ x 1 = 0 := by
    simp only [markedExtractionWeight, Nat.sub_self, Nat.cast_zero, zero_div,
      hzero, Complex.ofReal_zero, zero_mul]
  unfold markedActualRoughThetaSum markedActualPrimeThetaSum markedActualCompositeThetaSum
    roughPositiveUpTo actualCompositeThetaCoefficient
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hr : MarkedRoughAbove (x^γ) n
  · by_cases hp : n.Prime
    · simp only [hr, hp, ite_true, not_true_eq_false, and_false, ite_false, mul_zero, sub_self]
    · by_cases hn : n = 1
      · subst n
        simp only [hw1, zero_mul, sub_self, ite_self]
      · simp [hr, hp, hn]
  · have hw : n.Prime → markedExtractionWeight e G Φ x n = 0 := by
      intro hp
      by_contra hw
      exact hr (hx n hp hw)
    by_cases hp : n.Prime
    · simp only [hr, hp, ite_false, ite_true, hw hp, zero_mul, sub_self]
    · simp only [hr, hp, ite_false, sub_self]

end ArtinMatthews
