module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.EgyptianFractions.VanDerCorput
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

/-- A single multiplicative difference of a complex sequence. -/
def correlationShift (a : ℤ → ℂ) (h : ℤ) : ℤ → ℂ :=
  fun n => a (n + h) * conj (a n)

/-- Successive multiplicative differences, in their order of application. -/
def iteratedCorrelation (a : ℤ → ℂ) : List ℤ → ℤ → ℂ
  | [] => a
  | h :: hs => iteratedCorrelation (correlationShift a h) hs

theorem correlationShift_supported (a : ℤ → ℂ) (N : ℕ) (h : ℤ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) :
    ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → correlationShift a h n = 0 := by
  intro n hn
  simp [correlationShift, hsupport n hn]

theorem correlationShift_norm_le_one (a : ℤ → ℂ) (h : ℤ)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1) :
    ∀ n : ℤ, ‖correlationShift a h n‖ ≤ 1 := by
  intro n
  simp only [correlationShift, norm_mul, Complex.norm_conj]
  have h := mul_le_mul (hnorm (n + h)) (hnorm n) (norm_nonneg (a n)) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using h

/-- The elementary square-root budget obtained from repeated differencing. -/
def differencingBudget (H : ℕ) : ℕ → ℝ → ℝ
  | 0, B => B
  | r + 1, B => Real.sqrt (2 / (H : ℝ) + 2 * differencingBudget H r B)

theorem differencingBudget_nonneg (H r : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ differencingBudget H r B := by
  cases r with
  | zero => exact hB
  | succ r => exact Real.sqrt_nonneg _

/-- If every terminal `r`-fold correlation is small, the original sum is
    bounded by the iterated van der Corput square-root budget. -/
theorem iterated_differencing_bound (r : ℕ) (N H : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (B : ℝ) (hB : 0 ≤ B)
    (a : ℤ → ℂ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤ B) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ / (N : ℝ) ≤ differencingBudget H r B := by
  induction r generalizing a with
  | zero =>
    simpa [differencingBudget, iteratedCorrelation] using
      hterminal [] rfl (by simp)
  | succ r ih =>
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hbudget : 0 ≤ differencingBudget H r B := differencingBudget_nonneg H r hB
    have hcorr (h : ℤ) (hh : 0 < h) (hhH : h < H) :
        ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤
          (N : ℝ) * differencingBudget H r B := by
      have hchild := ih (correlationShift a h)
        (correlationShift_supported a N h hsupport)
        (correlationShift_norm_le_one a h hnorm) (by
          intro hs hlen hgood
          simpa [iteratedCorrelation] using hterminal (h :: hs) (by simp [hlen])
            (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro (And.intro hh hhH) hgood))
      have := (div_le_iff₀ hNR).mp hchild
      simpa [correlationShift, mul_comm] using this
    have hvdc := van_der_corput_interval_normalized a N H hH hHN
      ((N : ℝ) * differencingBudget H r B) (mul_nonneg (le_of_lt hNR) hbudget)
      hsupport hnorm hcorr
    have hcancel : 2 * ((N : ℝ) * differencingBudget H r B) / N =
        2 * differencingBudget H r B := by field_simp
    rw [hcancel, ← div_pow] at hvdc
    exact (Real.le_sqrt (div_nonneg (norm_nonneg _) (le_of_lt hNR)) (by positivity)).mpr hvdc

/-- A uniform bound for the square-root budget. Its constant does not grow
    with the number of differencing steps. -/
theorem differencingBudget_le_rpow (H r : ℕ) {ε B : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hHB : 2 / (H : ℝ) ≤ ε)
    (hB : B ≤ ε) :
    differencingBudget H r B ≤ 3 * ε ^ (1 / (2 : ℝ)^r) := by
  induction r with
  | zero =>
    simp only [differencingBudget, pow_zero, div_one, Real.rpow_one]
    linarith
  | succ r ih =>
    have hpow : (0 : ℝ) < (2 : ℝ)^r := by positivity
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ)^r := one_le_pow₀ (by norm_num)
    have halpha : 1 / (2 : ℝ)^r ≤ 1 := (div_le_one hpow).mpr hpow1
    have heps : ε ≤ ε ^ (1 / (2 : ℝ)^r) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 halpha
    have hpower : (ε ^ (1 / (2 : ℝ)^(r + 1)))^2 = ε ^ (1 / (2 : ℝ)^r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hε)]
      congr 1
      rw [pow_succ]
      field_simp
      norm_num
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · change 2 / (H : ℝ) + 2 * differencingBudget H r B ≤
        (3 * ε ^ (1 / (2 : ℝ)^(r + 1)))^2
      rw [mul_pow, hpower]
      have heps0 : 0 ≤ ε ^ (1 / (2 : ℝ)^r) := Real.rpow_nonneg (le_of_lt hε) _
      nlinarith

/-- Power-saving form of iterated van der Corput differencing. -/
theorem iterated_differencing_power_bound (r : ℕ) (N H : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hHε : 2 / (H : ℝ) ≤ ε) (a : ℤ → ℂ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤ ε) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ / (N : ℝ) ≤
      3 * ε ^ (1 / (2 : ℝ)^r) :=
  (iterated_differencing_bound r N H hH hHN ε (le_of_lt hε) a hsupport hnorm hterminal).trans
    (differencingBudget_le_rpow H r hε hε1 hHε le_rfl)

end Problem337

end

end OAI
