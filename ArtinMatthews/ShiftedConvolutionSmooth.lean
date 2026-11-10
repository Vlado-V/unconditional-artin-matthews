module

public import ArtinMatthews.ShiftedConvolutionNorm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Equation (5.6) for compact smooth cutoffs

The finite convolution is identified with the literal unrestricted coefficient
sum. Its rho sequence has finite support, so the stated square-sum is an actual
convergent series. Cutoff smoothness and support discharge all weight hypotheses.
-/

noncomputable section
open Complex UpperHalfPlane Real Set Finset
open scoped ContDiff

namespace ArtinMatthews

/-- A dyadic cutoff vanishes beyond the finite range used in the convolution. -/
theorem shiftedDyadicWeight_eq_zero (w : ℝ → ℂ) (hw : Function.support w ⊆ Icc 1 2)
    (K t : ℝ) (hK : 0 < K) (n : ℕ) (hn : shiftedDyadicLength K ≤ n) :
    shiftedDyadicWeight w K t n = 0 := by
  have hn' : 2 * K < (n : ℝ) := by
    have hceil := Nat.le_ceil (2 * K)
    have hn'' : (⌈2 * K⌉₊ : ℝ) + 1 ≤ n := by
      exact_mod_cast hn
    linarith
  have hz : w ((n : ℝ) / K) = 0 := by
    by_contra h
    have := (hw h).2
    have := (div_le_iff₀ hK).mp this
    linarith
  simp [shiftedDyadicWeight, hz]

/-- The totalized phase agrees with the paper's complex power after multiplying
by the cutoff, including the harmless zero-index term. -/
theorem shiftedDyadicWeight_eq_cpow (w : ℝ → ℂ) (hw : Function.support w ⊆ Icc 1 2)
    (K t : ℝ) (n : ℕ) :
    shiftedDyadicWeight w K t n = (n : ℂ) ^ (-(t : ℂ) * Complex.I) * w ((n : ℝ) / K) := by
  by_cases hn : n = 0
  · subst n
    have hz : w 0 = 0 := by
      by_contra h
      have := (hw h).1
      norm_num at this
    simp [shiftedDyadicWeight, hz]
  · exact congrArg (fun z : ℂ ↦ z * w ((n : ℝ) / K))
      (shiftedMellinPhase_eq_cpow t n (by exact_mod_cast Nat.pos_of_ne_zero hn))

/-- Finite ranges produce only finitely many actual convolution frequencies. -/
theorem shiftedConvolutionCoeff_hasFiniteSupport (S T : Finset ℕ) (m3 m4 D : ℕ)
    (a b : ℕ → ℂ) : Function.HasFiniteSupport (shiftedConvolutionCoeff S T m3 m4 D a b) := by
  classical
  let R := (S.product T).image (fun p ↦ (m4 : ℤ) * p.2 - (m3 : ℤ) * p.1)
  apply R.finite_toSet.subset
  intro r hr
  by_contra hn
  apply hr
  unfold shiftedConvolutionCoeff
  apply sum_eq_zero
  intro k1 hk1
  apply sum_eq_zero
  intro k2 hk2
  have hf : (m4 : ℤ) * k2 - (m3 : ℤ) * k1 ≠ r := by
    intro he
    apply hn
    exact mem_image.mpr ⟨(k1, k2), mem_product.mpr ⟨hk1, hk2⟩, he⟩
  simp [hf]

/-- The coefficient energy is a convergent series independently of any estimate. -/
theorem dyadicCuspConvolution_summable_sq
    {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ 1)
    (w1 w2 : ℝ → ℂ) (K1 K2 t1 t2 : ℝ) (m3 m4 D : ℕ) :
    Summable (fun r : ℤ ↦ ‖dyadicCuspConvolution f w1 w2 K1 K2 t1 t2 m3 m4 D r‖ ^ 2) := by
  apply summable_of_hasFiniteSupport
  have h := shiftedConvolutionCoeff_hasFiniteSupport
    (range (shiftedDyadicLength K1)) (range (shiftedDyadicLength K2)) m3 m4 D
    (fun k ↦ (qExpansion 1 f).coeff k * shiftedDyadicWeight w1 K1 t1 k)
    (fun k ↦ (qExpansion 1 f).coeff k * shiftedDyadicWeight w2 K2 t2 k)
  simpa only [Function.HasFiniteSupport, Function.support, ne_eq, sq_eq_zero_iff,
    norm_eq_zero, dyadicCuspConvolution] using h

/-- Exact equality with the unrestricted two-index sum defining Aρ in the paper. -/
theorem dyadicCuspConvolution_eq_tsum
    {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ 1)
    (w1 w2 : ℝ → ℂ) (hw1 : Function.support w1 ⊆ Icc 1 2)
    (hw2 : Function.support w2 ⊆ Icc 1 2)
    (K1 K2 t1 t2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (m3 m4 D : ℕ) (r : ℤ) :
    dyadicCuspConvolution f w1 w2 K1 K2 t1 t2 m3 m4 D r =
      ∑' k1 : ℕ, ∑' k2 : ℕ,
        if (m4 : ℤ) * k2 - (m3 : ℤ) * k1 = r ∧
            (m3 ^ 2 * k1 : ZMod D) = (m4 ^ 2 * k2 : ZMod D)
        then ((qExpansion 1 f).coeff k1 * shiftedDyadicWeight w1 K1 t1 k1) *
          ((qExpansion 1 f).coeff k2 * shiftedDyadicWeight w2 K2 t2 k2)
        else 0 := by
  symm
  rw [tsum_eq_sum (s := range (shiftedDyadicLength K1)) (fun k1 hk1 ↦ by
    have hz := shiftedDyadicWeight_eq_zero w1 hw1 K1 t1 hK1 k1 (by simpa using hk1)
    simp [hz])]
  unfold dyadicCuspConvolution shiftedConvolutionCoeff
  apply sum_congr rfl
  intro k1 _
  exact tsum_eq_sum (s := range (shiftedDyadicLength K2)) (fun k2 hk2 ↦ by
    have hz := shiftedDyadicWeight_eq_zero w2 hw2 K2 t2 hK2 k2 (by simpa using hk2)
    simp [hz])

/-- The same unrestricted formula with the literal Mellin powers k^(-it). -/
theorem dyadicCuspConvolution_eq_tsum_cpow
    {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ 1)
    (w1 w2 : ℝ → ℂ) (hw1 : Function.support w1 ⊆ Icc 1 2)
    (hw2 : Function.support w2 ⊆ Icc 1 2)
    (K1 K2 t1 t2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (m3 m4 D : ℕ) (r : ℤ) :
    dyadicCuspConvolution f w1 w2 K1 K2 t1 t2 m3 m4 D r =
      ∑' k1 : ℕ, ∑' k2 : ℕ,
        if (m4 : ℤ) * k2 - (m3 : ℤ) * k1 = r ∧
            (m3 ^ 2 * k1 : ZMod D) = (m4 ^ 2 * k2 : ZMod D)
        then ((qExpansion 1 f).coeff k1 *
          ((k1 : ℂ) ^ (-(t1 : ℂ) * Complex.I) * w1 ((k1 : ℝ) / K1))) *
            ((qExpansion 1 f).coeff k2 *
              ((k2 : ℂ) ^ (-(t2 : ℂ) * Complex.I) * w2 ((k2 : ℝ) / K2)))
        else 0 := by
  rw [dyadicCuspConvolution_eq_tsum f w1 w2 hw1 hw2 K1 K2 t1 t2 hK1 hK2 m3 m4 D r]
  simp_rw [shiftedDyadicWeight_eq_cpow w1 hw1, shiftedDyadicWeight_eq_cpow w2 hw2]

/-- The precise smooth-cutoff version of (5.6), without Schwartz data or an
assumed coefficient, additive, or spectral estimate in its hypotheses. -/
theorem weightOne_smooth_dyadicConvolution_norm
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (w1 w2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ w1) (hs2 : ContDiff ℝ ∞ w2)
    (hw1 : Function.support w1 ⊆ Icc 1 2) (hw2 : Function.support w2 ⊆ Icc 1 2)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K1 K2 t1 t2 : ℝ), 1 ≤ K1 → 1 ≤ K2 →
      ∀ (m3 m4 D : ℕ) [NeZero D], 0 < m4 →
        Real.sqrt (∑' r : ℤ, ‖dyadicCuspConvolution f w1 w2 K1 K2 t1 t2 m3 m4 D r‖ ^ 2) ≤
          C * (K1 * K2) ^ ((1 + ν) / 2) * (1 + |t1| + |t2|) ^ 2 := by
  have hc1 : HasCompactSupport w1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hw1
  have hc2 : HasCompactSupport w2 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hw2
  exact weightOne_dyadicConvolution_norm f hperiod (hc1.toSchwartzMap hs1) (hc2.toSchwartzMap hs2)
    hw1 ν hν

end ArtinMatthews
