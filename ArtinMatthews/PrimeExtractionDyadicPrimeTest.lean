module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.PrimeExtractionRelevantBoxes
public import ArtinMatthews.PrimeExtractionSeparatedCoefficients
public import ArtinMatthews.PrimeExtractionCoefficientInput
public import ArtinMatthews.PrimeExtractionRelevantGeometry
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

/-! The actual section-eight dyadic coefficients satisfy the long character
criterion, uniformly after restriction to any integer interval. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths Filter
open scoped BigOperators Classical

theorem primeExtractionDyadicBlock_inter_interval (N k m n : ℕ) :
    primeExtractionDyadicBlock N k ∩ Finset.Icc m n =
      Finset.Icc (max (2^k) m) (min (min N (2*2^k-1)) n) := by
  rw [primeExtractionDyadicBlock_eq_Ico]
  have hp : 0 < 2^k := by positivity
  ext d
  simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_Icc, max_le_iff, le_min_iff,
    lt_min_iff]
  omega

theorem primeExtractionRelevantBoxes_interval_tests (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B D R a T γ : ℝ) (hT : 0 ≤ T) (hγ : 0 < γ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop,
      ∀ kl ∈ primeExtractionRelevantBoxes ⌊T*x⌋₊ a γ x,
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (m n : ℕ) (v t : ℝ),
      |v| ≤ (Real.log x)^R →
      |t| ≤ 2*primeExtractionDyadicHeight kl.1 kl.2*(Real.log x)^B →
      ‖markedTwistedSum (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1 ∩ Finset.Icc m n)
        (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ (x^γ) v)
        ϑ t‖ / (2 : ℝ)^kl.1 ≤ 35*(Real.log x)^(-D) := by
  filter_upwards [primeExtractionFirstPhaseCoefficient_criterion A hA hnoncube χ
      A₀ B (γ/2) D R T γ (by linarith) hD,
    primeExtractionRelevantBoxes_geometry_eventually (a:=a) hT hγ,
    eventually_gt_atTop (1 : ℝ)] with x htest hgeometry hx
  intro kl hkl q _ hq ϑ m n v t hv ht
  have hg := hgeometry kl hkl
  rw [primeExtractionDyadicBlock_inter_interval]
  by_cases hmn : max (2^kl.1) m ≤ min (min ⌊T*x⌋₊ (2*2^kl.1-1)) n
  · apply htest q hq ϑ (primeExtractionDyadicHeight kl.1 kl.2) ((2:ℝ)^kl.1)
      hg.2.1 hg.2.2.1 _ _ hmn _ _ v t hv ht
    · exact_mod_cast (le_max_left (2^kl.1) m)
    · have hb : min (min ⌊T*x⌋₊ (2*2^kl.1-1)) n ≤ 2*2^kl.1 := by omega
      exact_mod_cast hb
  · rw [Finset.Icc_eq_empty hmn]
    simp only [markedTwistedSum, Finset.sum_empty, norm_zero, zero_div]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.log_pos hx).le _)

theorem primeExtractionRelevantBoxes_prime_tests (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B D R a T γ : ℝ) (hT : 0 ≤ T) (hγ : 0 < γ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop,
      ∀ kl ∈ primeExtractionRelevantBoxes ⌊T*x⌋₊ a γ x,
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (v t : ℝ),
      |v| ≤ (Real.log x)^R →
      |t| ≤ 2*primeExtractionDyadicHeight kl.1 kl.2*(Real.log x)^B →
      ‖markedTwistedSum (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1)
        (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ (x^γ) v)
        ϑ t‖ / (2 : ℝ)^kl.1 ≤ 35*(Real.log x)^(-D) := by
  filter_upwards [primeExtractionRelevantBoxes_interval_tests A hA hnoncube χ
    A₀ B D R a T γ hT hγ hD] with x htest
  intro kl hkl q _ hq ϑ v t hv ht
  have heq : primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1 ∩ Finset.Icc 0 ⌊T*x⌋₊ =
      primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1 := by
    apply Finset.inter_eq_left.mpr
    intro m hm
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2⟩
  simpa only [heq] using htest kl hkl q hq ϑ 0 ⌊T*x⌋₊ v t hv ht

theorem primeExtractionRelevantBoxes_conjugate_tests (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B D R a T γ : ℝ) (hT : 0 ≤ T) (hγ : 0 < γ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop,
      ∀ kl ∈ primeExtractionRelevantBoxes ⌊T*x⌋₊ a γ x,
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (m n : ℕ) (v t : ℝ),
      |v| ≤ (Real.log x)^R →
      |t| ≤ 2*primeExtractionDyadicHeight kl.1 kl.2*(Real.log x)^B →
      ‖markedTwistedSum (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1 ∩ Finset.Icc m n)
        (fun d => (starRingEnd ℂ) (primeExtractionFirstPhaseCoefficient
          (cubicNumeratorHeckeCharacter A hA) χ (x^γ) v d))
        ϑ t‖ / (2 : ℝ)^kl.1 ≤ 35*(Real.log x)^(-D) := by
  filter_upwards [primeExtractionRelevantBoxes_interval_tests A hA hnoncube χ
    A₀ B D R a T γ hT hγ hD] with x htest
  intro kl hkl q _ hq ϑ m n v t hv ht
  have h := htest kl hkl q hq (star ϑ) m n v (-t) hv (by simpa only [abs_neg] using ht)
  have heq := markedTwistedSum_norm_conjugate
    (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1 ∩ Finset.Icc m n)
    (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ (x^γ) v)
    (star ϑ) t
  simp only [star_star] at heq
  rw [heq]
  exact h

end ArtinMatthews
