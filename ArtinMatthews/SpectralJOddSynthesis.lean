module

public import ArtinMatthews.SpectralJOddCoefficients
public import ArtinMatthews.SpectralJIntegerSeries
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace ArtinMatthews

open Filter Set
noncomputable section

/-- The odd-order discrete Bessel term in the forward-J inversion. -/
def spectralJOddSynthesisTerm (f : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (2 : ℂ) * ((2 * k + 1 : ℕ) : ℂ) *
    spectralJDiscreteCoefficient f (2 * k + 1) *
    Complex.besselJ ((2 * k + 1 : ℕ) : ℂ) (x : ℂ)

/-- The odd-order part of the forward-J synthesis. -/
def spectralJOddSynthesis (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℕ, spectralJOddSynthesisTerm f k x

theorem spectralJOddSynthesisTerm_continuous (f : ℝ → ℂ) (k : ℕ) :
    Continuous (spectralJOddSynthesisTerm f k) :=
  continuous_const.mul
    ((spectral_besselJ_nat_continuous (2 * k + 1)).comp Complex.continuous_ofReal)

theorem spectralJOddSynthesisTerm_norm_le (f : ℝ → ℂ) {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hcoeff : ∀ n : ℕ, ‖spectralJDiscreteCoefficient f n‖ ≤ C * A ^ n / (n.factorial : ℝ))
    (k : ℕ) (x : ℝ) :
    ‖spectralJOddSynthesisTerm f k x‖ ≤
      2 * C * Real.exp (x ^ 2 / 4) * ((A * (|x| / 2)) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) := by
  let n : ℕ := 2 * k + 1
  change ‖(2 : ℂ) * (n : ℂ) * spectralJDiscreteCoefficient f n *
    Complex.besselJ (n : ℂ) (x : ℂ)‖ ≤
    2 * C * Real.exp (x ^ 2 / 4) * ((A * (|x| / 2)) ^ n / (n.factorial : ℝ))
  have hcast : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by norm_num [Complex.ofReal_div]
  have hnorm : ‖(x : ℂ) / 2‖ = |x| / 2 := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hsq : (|x| / 2) ^ 2 = x ^ 2 / 4 := by
    rw [div_pow, sq_abs]
    norm_num
  have hJ : ‖Complex.besselJ (n : ℂ) (x : ℂ)‖ ≤
      (|x| / 2) ^ n / (n.factorial : ℝ) * Real.exp (x ^ 2 / 4) := by
    simpa only [hnorm, hsq] using spectral_besselJ_nat_norm_le n (x : ℂ)
  have hn : (n : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial n
  have hnle : (n : ℝ) / (n.factorial : ℝ) ≤ 1 := div_le_one_of_le₀ hn (by positivity)
  calc
    _ = 2 * (n : ℝ) * ‖spectralJDiscreteCoefficient f n‖ *
        ‖Complex.besselJ (n : ℂ) (x : ℂ)‖ := by
      have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by
        simpa only [Nat.cast_ofNat] using Complex.norm_natCast 2
      simp only [norm_mul, Complex.norm_natCast, htwo]
    _ ≤ 2 * (n : ℝ) * (C * A ^ n / (n.factorial : ℝ)) *
        ((|x| / 2) ^ n / (n.factorial : ℝ) * Real.exp (x ^ 2 / 4)) := by
      gcongr
      exact hcoeff n
    _ = ((n : ℝ) / (n.factorial : ℝ)) *
        (2 * C * Real.exp (x ^ 2 / 4) * ((A * (|x| / 2)) ^ n / (n.factorial : ℝ))) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hnle

/-- A geometric majorant that also controls the Gaussian-weighted series. -/
theorem spectralJOddSynthesisTerm_norm_le_geometric (f : ℝ → ℂ) {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hcoeff : ∀ n : ℕ, ‖spectralJDiscreteCoefficient f n‖ ≤ C * A ^ n / (n.factorial : ℝ))
    (k : ℕ) (x : ℝ) :
    ‖spectralJOddSynthesisTerm f k x‖ ≤
      (1 / 2 : ℝ) ^ k * (2 * C * Real.exp (x ^ 2 / 4 + A * |x|)) := by
  let n : ℕ := 2 * k + 1
  let t : ℝ := A * |x|
  have ht : 0 ≤ t := mul_nonneg hA (abs_nonneg x)
  have hsum : HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ)) (Real.exp t) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t
  have hterm : t ^ n / (n.factorial : ℝ) ≤ Real.exp t := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.le_tsum n fun m hm => by positivity
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (show k ≤ 2 * k + 1 by omega)
  calc
    _ ≤ 2 * C * Real.exp (x ^ 2 / 4) * ((A * (|x| / 2)) ^ n / (n.factorial : ℝ)) :=
      spectralJOddSynthesisTerm_norm_le f hC hA hcoeff k x
    _ = (1 / 2 : ℝ) ^ n *
        (2 * C * Real.exp (x ^ 2 / 4) * (t ^ n / (n.factorial : ℝ))) := by
      rw [show A * (|x| / 2) = (1 / 2 : ℝ) * t by dsimp [t]; ring, mul_pow]
      ring
    _ ≤ (1 / 2 : ℝ) ^ k * (2 * C * Real.exp (x ^ 2 / 4) * Real.exp t) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem spectralJOddSynthesis_summable_norm (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    Summable (fun k : ℕ => ‖spectralJOddSynthesisTerm f k x‖) := by
  obtain ⟨C, A, hC, hA, hcoeff⟩ := spectralJDiscreteCoefficient_factorial_bound f hf hc hp
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => spectralJOddSynthesisTerm_norm_le_geometric f hC hA hcoeff k x)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_right _)

theorem spectralJOddSynthesis_tendstoUniformlyOn (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => ∑ k ∈ Finset.range N, spectralJOddSynthesisTerm f k x)
      (spectralJOddSynthesis f) atTop (Icc (-R) R) := by
  obtain ⟨C, A, hC, hA, hcoeff⟩ := spectralJDiscreteCoefficient_factorial_bound f hf hc hp
  refine tendstoUniformlyOn_tsum_nat
    (u := fun k => (1 / 2 : ℝ) ^ k * (2 * C * Real.exp (R ^ 2 / 4 + A * R)))
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_right _)
    ?_
  intro k x hx
  have habs : |x| ≤ R := abs_le.mpr hx
  have hsq : x ^ 2 ≤ R ^ 2 := by rw [← sq_abs x]; exact (sq_le_sq₀ (abs_nonneg _) hR).mpr habs
  exact (spectralJOddSynthesisTerm_norm_le_geometric f hC hA hcoeff k x).trans (by gcongr)

theorem spectralJOddSynthesis_continuous (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Continuous (spectralJOddSynthesis f) := by
  rw [continuous_iff_continuousAt]
  intro x
  let R : ℝ := |x| + 1
  have hx : x ∈ Ioo (-R) R := abs_lt.mp (by dsimp [R]; linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcont : ContinuousOn (spectralJOddSynthesis f) (Icc (-R) R) :=
    (spectralJOddSynthesis_tendstoUniformlyOn f hf hc hp R hR).continuousOn
      (Frequently.of_forall fun N =>
        (continuous_finsetSum _ fun k _ => spectralJOddSynthesisTerm_continuous f k).continuousOn)
  exact hcont.continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self)

end
end ArtinMatthews
