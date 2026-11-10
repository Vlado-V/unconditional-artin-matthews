module

public import ArtinMatthews.PositiveDensityCubicCuspBaseline
public import ArtinMatthews.CubicSievePrimeReindex
public import ArtinMatthews.CubicSievePrimeCorrelation
public import ArtinMatthews.PositiveDensityCubicCuspCharacter
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
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! The same actual source coefficient estimate controls the literal
centered and uncentered native cubic cusp statistics on fixed progressions. -/

noncomputable section
namespace ArtinMatthews

open Filter Finset UpperHalfPlane OAI OAI.SevenEighths
open scoped BigOperators ContDiff Topology Asymptotics MatrixGroups

theorem cubicSieve_prime_test_eq_predecessor_correlation (H : ℕ → ℂ) (Φ : ℝ → ℝ)
    {T x : ℝ} (hT₁ : 1 < T) (hT : T < 2) (hs : Function.support Φ ⊆ Set.Ioo 1 T) (hx : 1 ≤ x) :
    (∑ p ∈ giantPrimeMeanRange T x, (Φ (((p - 1 : ℕ) : ℝ) / x) : ℂ) * H (p - 1)) =
      ∑ u ∈ (Icc 0 ⌊2 * x⌋₊).filter (fun u => (u + 1).Prime), (Φ ((u : ℝ) / x) : ℂ) * H u := by
  let P := giantPrimeMeanRange T x
  let Q := (Ioc 0 ⌊3 * x⌋₊).filter Nat.Prime
  let f (p : ℕ) := (Φ (((p - 1 : ℕ) : ℝ) / x) : ℂ) * H (p - 1)
  have hx₀ := zero_lt_one.trans_le hx
  have hTx : T * x ≤ 2 * x := mul_le_mul_of_nonneg_right hT.le hx₀.le
  have hcap : ⌊T * x⌋₊ + 1 ≤ ⌊3 * x⌋₊ := by
    apply Nat.le_floor
    have h := Nat.floor_le (mul_nonneg (zero_lt_one.trans hT₁).le hx₀.le)
    push_cast
    linarith
  have hsub : P ⊆ Q := by
    intro p hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    obtain ⟨_, hpn⟩ := mem_Icc.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hprime.pos, hpn.trans hcap⟩, hprime⟩
  have heq : (∑ p ∈ P, f p) = ∑ p ∈ Q, f p := by
    apply sum_subset hsub
    intro p hp hn
    by_contra hf
    have hφ : Φ (((p - 1 : ℕ) : ℝ) / x) ≠ 0 := by
      intro hz
      exact hf (by simp only [f, hz, Complex.ofReal_zero, zero_mul])
    have hpred : p - 1 ≤ ⌊T * x⌋₊ := Nat.le_floor ((div_lt_iff₀ hx₀).mp (hs hφ).2).le
    obtain ⟨_, hprime⟩ := mem_filter.mp hp
    exact hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, hprime⟩)
  exact heq.trans (cubicSieve_prime_predecessor_sum H Φ
    (hs.trans (fun _ ht => ⟨ht.1, ht.2.trans hT⟩)) hx)

theorem cubicSieve_actual_cusp_centered_eq_correlation
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} (χ : DirichletCharacter ℂ M) {ε T x : ℝ}
    (hε : ε ≤ 1 / 4) (hT₁ : 1 < T) (hT₂ : T < 2)
    (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 T) (hx : 4 ≤ x) :
    giantCubicCuspCenteredPrimeTest (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)
      (fun p => χ p) ε Φ T x =
    markedPrimeCorrelation Φ 2
      (giantCubicCenteredPrimeCoefficient (cubicNumeratorHeckeCharacter A hA) χ ε) x := by
  let η := cubicNumeratorHeckeCharacter A hA
  let H := giantCubicCenteredPrimeCoefficient η χ ε x
  have hx₀ : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have heq : giantCubicCuspCenteredPrimeTest (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)
      (fun p => χ p) ε Φ T x =
      ∑ p ∈ giantPrimeMeanRange T x, (Φ (((p - 1 : ℕ) : ℝ) / x) : ℂ) * H (p - 1) := by
    unfold giantCubicCuspCenteredPrimeTest
    apply sum_congr rfl
    intro p hp
    have hprime := (mem_filter.mp hp).2
    have hp₁ : 1 ≤ p := hprime.one_lt.le
    rw [actualCubicNumeratorHeckeThetaCuspForm_qExpansion_coeff]
    by_cases hφ : Φ (((p - 1 : ℕ) : ℝ) / x) = 0
    · simp only [giantSieveWeight, Nat.cast_sub hp₁, Nat.cast_one] at hφ ⊢
      simp only [hφ, Complex.ofReal_zero, zero_mul]
    · have hlow := (lt_div_iff₀ hx₀).mp (hs hφ).1
      have hhi := (div_lt_iff₀ hx₀).mp (hs hφ).2
      have hu : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
      have hux : ((p - 1 : ℕ) : ℝ) ≤ 2 * x := hhi.le.trans (mul_le_mul_of_nonneg_right hT₂.le hx₀.le)
      dsimp only [H, giantCubicCenteredPrimeCoefficient, giantMarkedCenteredCore]
      rw [boundedGiantIndicator_eq_card hu hux hx hε, Nat.sub_add_cancel hp₁]
      simp only [giantSieveWeight, Nat.cast_sub hp₁, Nat.cast_one]
      dsimp only [η]
      ring
  rw [heq, cubicSieve_prime_test_eq_predecessor_correlation H Φ hT₁ hT₂ hs (by linarith)]
  rfl

theorem cubicSieve_actual_cusp_centered_source_isLittleO
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε T : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) (hT₁ : 1 < T) (hT₂ : T < 2)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 T)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) :
    giantCubicCuspCenteredPrimeTest (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)
      (fun p => χ p) ε Φ T =o[atTop] (fun x : ℝ => x / Real.log x) := by
  have h := cubicSieve_actual_prime_correlation_isLittleO A hA hnoncube χ hε hεq Φ hΦ hΦ₀ hΦ₁
    (hs.trans (fun _ ht => ⟨ht.1, ht.2.trans hT₂⟩)) hsource
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  exact (cubicSieve_actual_cusp_centered_eq_correlation A hA hnoncube χ hεq.le hT₁ hT₂ Φ hs hx).symm

theorem cubicSieve_actual_cusp_source_mean
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε T : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) (hT₁ : 1 < T) (hT₂ : T < 2)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 T)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantCubicCuspPrimeTest (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)
        (fun p => χ p) ε Φ T x) atTop (𝓝 0) := by
  have hc : HasCompactSupport Φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hs.trans Set.Ioo_subset_Icc_self)
  exact giantCubicCuspPrimeTest_mean_of_centered A hA hnoncube χ hε (hεq.trans (by norm_num))
    Φ hΦ hc hT₁ hs
    (cubicSieve_actual_cusp_centered_source_isLittleO A hA hnoncube χ hε hεq hT₁ hT₂
      Φ hΦ hΦ₀ hΦ₁ hs hsource)

theorem cubicSieve_actual_cusp_source_progression_mean
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ)
    {ε T : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) (hT₁ : 1 < T) (hT₂ : T < 2)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 T)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantCubicCuspPrimeTest (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)
        (fun p => giantUnitResidueIndicator U p) ε Φ T x) atTop (𝓝 0) :=
  giantCubicCuspPrimeTest_mean_of_character_limits _ U ε Φ T
    (fun χ => cubicSieve_actual_cusp_source_mean A hA hnoncube χ hε hεq hT₁ hT₂ Φ hΦ hΦ₀ hΦ₁ hs hsource)

end ArtinMatthews
