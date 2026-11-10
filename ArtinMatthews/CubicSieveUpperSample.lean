module

public import ArtinMatthews.CubicSieveUpper
public import ArtinMatthews.MarkedOrderedLimits
public import ArtinMatthews.CubicSamplingCentered
public import ArtinMatthews.GiantSamplingShiftedInput
public import ArtinMatthews.CubicSamplingProposition61
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

/-! Exact upper-polynomial insertion in the actual centered cubic
coefficient sum. Distinct prime subsets give distinct positive moduli in
the available Proposition 6.1 range. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths OAI.Erdos970.NumberTheoryLean
open scoped BigOperators ContDiff

def cubicSieveSourceExponent (ε : ℝ) (m : ℕ) : ℝ :=
  markedCorrelationSieveExponent (ε / 64) (2 * (m : ℝ))

theorem cubicSieve_sourceExponent_bounds {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) (m : ℕ) :
    0 < cubicSieveSourceExponent ε m ∧ cubicSieveSourceExponent ε m < 1 / 2 ∧
      cubicSieveSourceExponent ε m * (8 * (m : ℝ) + 2) ≤ ε / 64 := by
  unfold cubicSieveSourceExponent markedCorrelationSieveExponent
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hd : 0 < 4 * (2 * (m : ℝ)) + 3 := by positivity
  refine ⟨div_pos (by positivity) hd, ?_, ?_⟩
  · apply (div_lt_iff₀ hd).mpr
    nlinarith
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hd).mpr (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

def cubicSieveUpperThetaSum (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε γ x : ℝ) (m : ℕ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, H u * giantMarkedCenteredCore ε x u *
    giantCubicSamplingKernel η χ Φ x 1 u * (cubicSieveUpper (x ^ γ) m (u + 1) : ℂ)

theorem cubicSieve_upperTheta_eq_progressions (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε γ x : ℝ) (m : ℕ) :
    cubicSieveUpperThetaSum η χ H Φ ε γ x m =
      ∑ T ∈ cubicSieveUpperSupport (x ^ γ) m, (cubicSieveUpperCoeff (x ^ γ) m T : ℂ) *
        giantCubicSamplingCenteredSum η χ H Φ ε x (roughSubsetDivisor T) := by
  unfold cubicSieveUpperThetaSum giantCubicSamplingCenteredSum
  simp_rw [cubicSieve_upper_eq_divisor_sum, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _hT
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases h : roughSubsetDivisor T ∣ u + 1
  · simp only [giantCubicSamplingKernel, one_dvd, ite_eq_left, h]
    ring
  · simp only [giantCubicSamplingKernel, ite_eq_right h, mul_zero]

theorem cubicSieve_upperTheta_norm_le (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε : ℝ)
    {γ x c : ℝ} (hx : 1 < x) (hγ : 0 < γ) (m : ℕ) (hlevel : γ * (8 * (m : ℝ)) ≤ c) :
    ‖cubicSieveUpperThetaSum η χ H Φ ε γ x m‖ ≤
      ∑ r ∈ Finset.Icc 1 ⌊x ^ c⌋₊, ‖giantCubicSamplingCenteredSum η χ H Φ ε x r‖ := by
  let z := x ^ γ
  let S := cubicSieveUpperSupport z m
  let P := Nat.primesLE ⌊z⌋₊
  let R := Finset.Icc 1 ⌊x ^ c⌋₊
  let F (r : ℕ) := giantCubicSamplingCenteredSum η χ H Φ ε x r
  have hz : 1 < z := Real.one_lt_rpow hx hγ
  have hR (T : Finset ℕ) (hT : T ∈ S) : roughSubsetDivisor T ∈ R := by
    obtain ⟨hpos, _hsq, hsize⟩ := cubicSieve_upperSupport_level hz hT
    refine Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor ?_⟩
    calc
      _ ≤ z ^ (8 * (m : ℝ)) := hsize
      _ = x ^ (γ * (8 * (m : ℝ))) := (Real.rpow_mul (zero_le_one.trans hx.le) _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le hlevel
  have hsub : S.image roughSubsetDivisor ⊆ R := by
    intro d hd
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hd
    exact hR T hT
  have hinj : Set.InjOn roughSubsetDivisor (S : Set (Finset ℕ)) :=
    (DisjointBlockExpansion.prime_product_injective P
      (fun p hp => (Nat.mem_primesLE.mp hp).2)).mono (fun T hT => (Finset.mem_filter.mp hT).1)
  rw [cubicSieve_upperTheta_eq_progressions]
  change ‖∑ T ∈ S, (cubicSieveUpperCoeff z m T : ℂ) * F (roughSubsetDivisor T)‖ ≤ _
  calc
    _ ≤ ∑ T ∈ S, ‖(cubicSieveUpperCoeff z m T : ℂ) * F (roughSubsetDivisor T)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ T ∈ S, ‖F (roughSubsetDivisor T)‖ := by
      apply Finset.sum_le_sum
      intro T _hT
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (cubicSieve_upperCoeff_abs_le z m T)
    _ = ∑ r ∈ S.image roughSubsetDivisor, ‖F r‖ :=
      (Finset.sum_image (f := fun r => ‖F r‖) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)

theorem cubicSieve_upperTheta_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν)
    (m : ℕ) (G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ‖cubicSieveUpperThetaSum (cubicNumeratorHeckeCharacter A hA) χ
        (fun u => (literalMarkedArrayWeight e x u : ℂ)) Φ ε (cubicSieveSourceExponent ε m) x m‖ ≤
        x * (Real.log x) ^ (-G) := by
  obtain ⟨hγ, _hγ₁, hlevel⟩ := cubicSieve_sourceExponent_bounds hε hεq m
  have hlevel' : cubicSieveSourceExponent ε m * (8 * (m : ℝ)) ≤ ε / 64 :=
    (mul_le_mul_of_nonneg_left (by linarith) hγ.le).trans hlevel
  filter_upwards [giantCubicSampling_literalArray_centered_log_saving e he A hA hnoncube χ
    hε hεq Φ hΦ hΦ₁ hs hsource G, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  exact (cubicSieve_upperTheta_norm_le _ χ _ Φ ε hx₁ hγ m hlevel').trans hx

end ArtinMatthews
