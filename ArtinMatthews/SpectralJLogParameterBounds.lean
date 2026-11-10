module

public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SpectralJLogSeminorm
public import ArtinMatthews.SpectralJLogTransformBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Polynomial spectral decay and logarithmic scale absorption for the
actual fixed logarithmic source family. -/
namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

theorem spectralJOscillatoryLogProfile_real_decay
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u t Z : ℝ, 0 < a → a ≤ R → 1+|u| ≤ Z →
      ‖spectralJForwardTransform (spectralJOscillatoryLogProfile A B a u) (t : ℂ)‖ ≤
        C*(1+|Real.log a|)/(1+|t|/Z)^N := by
  obtain ⟨D,hD,hbase⟩ := spectralJOscillatoryLogProfile_real_basic A B hA hB hs R hR
  obtain ⟨E,hE,hpower⟩ := spectralJOscillatoryLogProfile_real_power A B hA hB hs R hR N
  refine ⟨D*2^N+E+1, by positivity, ?_⟩
  intro a u t Z ha haR hZ
  have hZ₁ : 1 ≤ Z := (by linarith [abs_nonneg u] : 1 ≤ 1+|u|).trans hZ
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ₁
  have hratio₀ : 0 < 1+|t|/Z := by positivity
  have hratio₁ : 1 ≤ 1+|t|/Z := by linarith [div_nonneg (abs_nonneg t) hZ₀.le]
  let y := ‖spectralJForwardTransform (spectralJOscillatoryLogProfile A B a u) (t : ℂ)‖
  have hy : 0 ≤ y := norm_nonneg _
  have hL : 1 ≤ 1+|Real.log a| := by linarith [abs_nonneg (Real.log a)]
  apply (le_div_iff₀ (pow_pos hratio₀ N)).mpr
  change y*(1+|t|/Z)^N ≤ _
  rcases le_or_gt |t| Z with ht|ht
  · have hratio₂ : 1+|t|/Z ≤ 2 := by
      have h := (div_le_one hZ₀).mpr ht
      linarith
    calc
      _ ≤ (D*(1+|Real.log a|))*2^N :=
        mul_le_mul (hbase a u t ha haR) (pow_le_pow_left₀ hratio₀.le hratio₂ N)
          (pow_nonneg hratio₀.le N) (by positivity)
      _ ≤ _ := by
        nlinarith [mul_nonneg hE.le (zero_le_one.trans hL), mul_nonneg (by positivity : 0 ≤ D*2^N) (zero_le_one.trans hL)]
  · have ht₁ : 1 ≤ |t| := hZ₁.trans ht.le
    have hq : 1+|t|/Z ≤ 2*|t|/Z := by
      have h := (one_le_div hZ₀).mpr ht.le
      calc
        _ ≤ |t|/Z+|t|/Z := by linarith
        _ = _ := by ring
    have hpow : (1+|t|/Z)^N ≤ (2*|t|/Z)^(2*N) :=
      (pow_le_pow_left₀ hratio₀.le hq N).trans
        (pow_le_pow_right₀ (by
          have h := (one_le_div hZ₀).mpr ht.le
          calc
            1 ≤ 2*(|t|/Z) := by linarith
            _ = 2*|t|/Z := by ring) (by omega))
    have hidentity : (2*|t|/Z)^(2*N)*Z^(2*N) = (4*t^2)^N := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hZ₀.ne'), pow_mul]
      congr 1
      nlinarith [sq_abs t]
    have hscaled : y*(1+|t|/Z)^N ≤ E := by
      apply (mul_le_mul_iff_left₀ (pow_pos hZ₀ (2*N))).mp
      calc
        _ ≤ y*(2*|t|/Z)^(2*N)*Z^(2*N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hy) (pow_nonneg hZ₀.le _)
        _ = (4*t^2)^N*y := by rw [mul_assoc,hidentity]; ring
        _ ≤ E*(1+|u|)^(2*N) := hpower a u t ha haR ht₁
        _ ≤ E*Z^(2*N) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hZ (2*N)) hE.le
    exact hscaled.trans (by nlinarith [mul_nonneg (by positivity : 0 ≤ D*2^N) (zero_le_one.trans hL)])

theorem spectralJLogScale_absorb (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P a : ℝ, 1 ≤ P → 0 < a → a ≤ R → P⁻¹ ≤ a →
      1+|Real.log a| ≤ C*P^δ := by
  let S := max 1 R
  have hS : 1 ≤ S := le_max_left _ _
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  refine ⟨1+Real.log S+δ⁻¹, by positivity, ?_⟩
  intro P a hP ha haR hPa
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hpow : 1 ≤ P^δ := Real.one_le_rpow hP hδ.le
  have hloga : Real.log a ≤ Real.log S :=
    Real.log_le_log ha (haR.trans (le_max_right _ _))
  have hlower : -Real.log P ≤ Real.log a := by
    have h := Real.log_le_log (inv_pos.mpr hP₀) hPa
    rwa [Real.log_inv] at h
  have hlogP : Real.log P ≤ P^δ*δ⁻¹ := by
    simpa only [div_eq_mul_inv] using Real.log_le_rpow_div hP₀.le hδ
  have habs : |Real.log a| ≤ Real.log S+P^δ*δ⁻¹ := by
    apply abs_le.mpr
    constructor <;> nlinarith [inv_nonneg.mpr hδ.le]
  calc
    _ ≤ 1+Real.log S+P^δ*δ⁻¹ := by linarith
    _ ≤ (1+Real.log S+δ⁻¹)*P^δ := by
      nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 1+Real.log S)]

end
end ArtinMatthews
