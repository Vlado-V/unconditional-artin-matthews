module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.LargeSquareSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

namespace OAI

/-! Higher prime powers in the von Mangoldt replacement have sparse support,
even when the underlying prime is small. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primePower_norm_pow (p : Eisenstein) (j : ℕ) : norm (p^j) = norm p^j := by
  induction j with
  | zero => simp [norm]
  | succ j ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

/-- Extracting half the exponent produces a genuinely large square divisor.
The bound depends on the prime-power norm, not the prime norm. -/
lemma large_square_of_prime_power {p b : Eisenstein} (hp : p ≠ 0) {j : ℕ}
    (hj : 2 ≤ j) {Y c : ℝ} (hY : 0 < Y)
    (hlarge : Y^c < norm (p^j)) (hdiv : p^j ∣ b) :
    ∃ d : Eisenstein, Y^(c/4) < norm d ∧ d^2 ∣ b := by
  refine ⟨p^(j/2),?_,?_⟩
  · have he : j ≤ 4*(j/2) := by omega
    have hpow : norm (p^j) ≤ norm (p^(j/2))^4 := by
      rw [primePower_norm_pow,primePower_norm_pow,← pow_mul]
      rw [Nat.mul_comm (j/2) 4]
      exact pow_le_pow_right₀ (one_le_norm hp) he
    have hYpow : (Y^(c/4))^4 = Y^c := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY.le]
      congr 1
      norm_num
    by_contra! hn
    have hd := pow_le_pow_left₀ (norm_nonneg _) hn 4
    rw [hYpow] at hd
    exact (hlarge.trans_le hpow).not_ge hd
  · apply dvd_trans _ hdiv
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)

def largePrimePowerSupport (Y c : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall Y).filter (fun b => ∃ p : Eisenstein, ∃ j : ℕ,
    primaryPrime p ∧ 2 ≤ j ∧ Y^c < norm (p^j) ∧ p^j ∣ b)

lemma largePrimePowerSupport_subset {Y c : ℝ} (hY : 0 < Y) :
    largePrimePowerSupport Y c ⊆ largeSquareSupport Y (Y^(c/4)) := by
  intro b hb
  obtain ⟨hball,p,j,hp,hj,hlarge,hdiv⟩ := Finset.mem_filter.mp hb
  obtain ⟨d,hd,hdvd⟩ := large_square_of_prime_power hp.2.ne_zero hj hY hlarge hdiv
  exact Finset.mem_filter.mpr ⟨hball,d,hd,hdvd⟩

/-- A fixed positive power is saved for every higher-prime-power error support. -/
theorem largePrimePowerSupport_card_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y c : ℝ), 0 < Y →
      ((largePrimePowerSupport Y c).card:ℝ) ≤ K*Y^(1-c/8) := by
  obtain ⟨K,hK,hbound⟩ := largeSquareSupport_card_bound
  refine ⟨K,hK,?_⟩
  intro Y c hY
  have h := hbound Y (Y^(c/4)) hY.le (Real.rpow_pos_of_pos hY _)
  have hcard : ((largePrimePowerSupport Y c).card:ℝ) ≤
      ((largeSquareSupport Y (Y^(c/4))).card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (largePrimePowerSupport_subset hY))
  have he : K*Y*(Y^(c/4))^(-(1/2:ℝ)) = K*Y^(1-c/8) := by
    rw [mul_assoc]
    congr 1
    calc
      _ = Y^(1:ℝ)*Y^(c/4*(-(1/2:ℝ))) := by
        rw [Real.rpow_one,← Real.rpow_mul hY.le]
      _ = Y^(1+c/4*(-(1/2:ℝ))) := (Real.rpow_add hY _ _).symm
      _ = _ := by congr 1; ring
  exact hcard.trans (h.trans_eq he)

/-- Any bounded coefficients supported on these errors inherit the same
saving in their quadratic energy. -/
theorem primePowerError_energy_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y c A : ℝ), 0 < Y → 0 ≤ A →
      ∀ v : Eisenstein → ℂ, (∀ b ∈ largePrimePowerSupport Y c, ‖v b‖ ≤ A) →
      (∑ b ∈ largePrimePowerSupport Y c, ‖v b‖^2) ≤ K*Y^(1-c/8)*A^2 := by
  obtain ⟨K,hK,hbound⟩ := largePrimePowerSupport_card_bound
  refine ⟨K,hK,?_⟩
  intro Y c A hY hA v hv
  calc
    _ ≤ ∑ _b ∈ largePrimePowerSupport Y c, A^2 := Finset.sum_le_sum
      (fun b hb => pow_le_pow_left₀ (_root_.norm_nonneg _) (hv b hb) 2)
    _ = ((largePrimePowerSupport Y c).card:ℝ)*A^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound Y c hY) (sq_nonneg _)

end CubicFirstMoment

end

end OAI
