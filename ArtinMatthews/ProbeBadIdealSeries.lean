module

public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.ProbeBadIdealNormalSeries
public import ArtinMatthews.ProbeEulerLocalBounds
public import ArtinMatthews.ProbeIdealCoefficientBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual bad-prime head/tail estimate at every height-one prime ideal.
The finite coefficient identities, not a principal-generator assumption,
supply the cancellations and the two geometric sums. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probeBadIdealWeight_base (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (a b W V : ℂ) (m : ℕ) :
    probeIdealSourceWeight K P χ j a b W V 0 0 0 m = V ^ m := by
  simp [probeIdealSourceWeight, probeIdealLocalCoefficient_zero_zero]

theorem probeBadIdealWeight_zero_outer (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (hj : 0 < j)
    (a b W V : ℂ) (k m : ℕ) :
    probeIdealSourceWeight K P χ j a b W V 0 0 (k + 1) m = 0 := by
  simp only [probeIdealSourceWeight, Fin.val_zero, mul_zero, zero_add]
  rw [probeIdealLocalCoefficient_zero_bad_outer K P χ k _ (by omega)]
  simp

theorem probeBadIdealWeight_first_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (j : ℕ) (hj : 0 < j) (a b W V : ℂ) (m : ℕ) :
    probeIdealSourceWeight K P χ j a b W V 1 0 0 m = 0 := by
  simp only [probeIdealSourceWeight, Fin.val_one, mul_zero, add_zero]
  rw [probeIdealLocalCoefficient_bad_first_zero K P χ hχ _ (by omega)]
  simp

def probeBadIdealPair (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ)
    (a b W V : ℂ) (e k : Fin 2) (n : ℕ) (v : ℕ × ℕ) : ℂ :=
  probeIdealSourceWeight K P χ j a b W V e (v.1 + n) k.val v.2

theorem probeBadIdealPair_norm_bound (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ) (e k : Fin 2) (n : ℕ)
    (v : ℕ × ℕ) :
    ‖probeBadIdealPair K P χ j a b W V e k n v‖ ≤
      (probeBadE (Ideal.absNorm P.asIdeal) a ^ e.val *
        probeBadT (Ideal.absNorm P.asIdeal) W ^ k.val *
        probeBadA (Ideal.absNorm P.asIdeal) b ^ n) *
      (probeBadA (Ideal.absNorm P.asIdeal) b ^ v.1 * ‖V‖ ^ v.2) := by
  apply (probeBadIdealWeight_norm_le K P χ hχ hminus j a b W V e k (v.1 + n) v.2).trans_eq
  simp only [probeBadE, probeBadA, probeBadT, pow_add]
  ring

theorem probeBadIdealPair_summable (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b < 1) (hV : ‖V‖ < 1)
    (e k : Fin 2) (n : ℕ) :
    Summable (probeBadIdealPair K P χ j a b W V e k n) := by
  have hg := probe_geometric_pair_hasSum
    (by unfold probeBadA; positivity) hA (norm_nonneg V) hV
  exact Summable.of_norm_bounded (hg.mul_left
    (probeBadE (Ideal.absNorm P.asIdeal) a ^ e.val *
      probeBadT (Ideal.absNorm P.asIdeal) W ^ k.val *
      probeBadA (Ideal.absNorm P.asIdeal) b ^ n)).summable
    (probeBadIdealPair_norm_bound K P χ hχ hminus j a b W V e k n)

theorem probeBadIdealPair_tsum_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b < 1) (hV : ‖V‖ < 1)
    (e k : Fin 2) (n : ℕ) :
    ‖∑' v, probeBadIdealPair K P χ j a b W V e k n v‖ ≤
      (probeBadE (Ideal.absNorm P.asIdeal) a ^ e.val *
        probeBadT (Ideal.absNorm P.asIdeal) W ^ k.val *
        probeBadA (Ideal.absNorm P.asIdeal) b ^ n) *
      ((1 - probeBadA (Ideal.absNorm P.asIdeal) b)⁻¹ * (1 - ‖V‖)⁻¹) := by
  have hg := probe_geometric_pair_hasSum
    (by unfold probeBadA; positivity) hA (norm_nonneg V) hV
  exact tsum_of_norm_bounded (hg.mul_left _) (probeBadIdealPair_norm_bound K P χ hχ hminus j a b W V e k n)

def probeBadIdealLocalSeries (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑ k : Fin 2, ∑' v,
    probeBadIdealPair K P χ j a b W V e k 0 v

def probeBadIdealTail (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑ k : Fin 2, ∑' v,
    probeBadIdealPair K P χ j a b W V e k 1 v

theorem probeBadIdealLocalSeries_decompose (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b < 1) (hV : ‖V‖ < 1) :
    probeBadIdealLocalSeries K P χ j a b W V =
      (1 - V)⁻¹ + (∑' m : ℕ, probeIdealSourceWeight K P χ j a b W V 1 0 1 m) +
        probeBadIdealTail K P χ j a b W V := by
  have hh (e k : Fin 2) := probe_pair_tsum_head
    (probeBadIdealPair_summable K P χ hχ hminus j a b W V hA hV e k 0)
  have hd (e k : Fin 2) : (∑' v, probeBadIdealPair K P χ j a b W V e k 0 v) =
      (∑' m : ℕ, probeIdealSourceWeight K P χ j a b W V e 0 k.val m) +
        ∑' v, probeBadIdealPair K P χ j a b W V e k 1 v := by
    simpa only [probeBadIdealPair, add_zero] using hh e k
  unfold probeBadIdealLocalSeries probeBadIdealTail
  simp only [hd, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    probeBadIdealWeight_base, probeBadIdealWeight_zero_outer K P χ j hj,
    probeBadIdealWeight_first_zero K P χ hχ j hj, tsum_zero, zero_add]
  rw [(hasSum_geometric_of_norm_lt_one hV).tsum_eq]
  ring

theorem probeBadIdealTail_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b < 1) (hV : ‖V‖ < 1) :
    ‖probeBadIdealTail K P χ j a b W V‖ ≤
      (1 + probeBadE (Ideal.absNorm P.asIdeal) a) *
      (1 + probeBadT (Ideal.absNorm P.asIdeal) W) *
      probeBadA (Ideal.absNorm P.asIdeal) b *
      ((1 - probeBadA (Ideal.absNorm P.asIdeal) b)⁻¹ * (1 - ‖V‖)⁻¹) := by
  calc
    _ ≤ ∑ e : Fin 2, ∑ k : Fin 2,
        ‖∑' v, probeBadIdealPair K P χ j a b W V e k 1 v‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ e : Fin 2, ∑ k : Fin 2,
        (probeBadE (Ideal.absNorm P.asIdeal) a ^ e.val *
          probeBadT (Ideal.absNorm P.asIdeal) W ^ k.val *
          probeBadA (Ideal.absNorm P.asIdeal) b ^ 1) *
        ((1 - probeBadA (Ideal.absNorm P.asIdeal) b)⁻¹ * (1 - ‖V‖)⁻¹) :=
      Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun k _ =>
        probeBadIdealPair_tsum_norm_le K P χ hχ hminus j a b W V hA hV e k 1
    _ = _ := by simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]; ring

theorem probeBadIdealFirst_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ) (hV : ‖V‖ < 1) :
    ‖∑' m : ℕ, probeIdealSourceWeight K P χ j a b W V 1 0 1 m‖ ≤
      probeBadE (Ideal.absNorm P.asIdeal) a *
      probeBadT (Ideal.absNorm P.asIdeal) W * (1 - ‖V‖)⁻¹ := by
  apply tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (norm_nonneg V) hV).mul_left _)
  intro m
  simpa only [Fin.val_one, pow_one, pow_zero, mul_one, probeBadE, probeBadT, mul_assoc] using
    probeBadIdealWeight_norm_le K P χ hχ hminus j a b W V 1 1 0 m

def probeBadIdealCorrection (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  (1 - V) * probeBadIdealLocalSeries K P χ j a b W V

theorem probeBadIdealCorrection_sub_one (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b < 1) (hV : ‖V‖ < 1) :
    probeBadIdealCorrection K P χ j a b W V - 1 =
      (1 - V) * ((∑' m : ℕ, probeIdealSourceWeight K P χ j a b W V 1 0 1 m) +
        probeBadIdealTail K P χ j a b W V) := by
  have hV0 : 1 - V ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne norm (by simpa using hV.ne)).symm
  rw [probeBadIdealCorrection,
    probeBadIdealLocalSeries_decompose K P χ hχ hminus j hj a b W V hA hV,
    mul_add, mul_add, mul_inv_cancel₀ hV0]
  ring

theorem probeBadIdealCorrection_norm_sub_one_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm P.asIdeal) b ≤ 1 / 2) (hV : ‖V‖ ≤ 1 / 2) :
    ‖probeBadIdealCorrection K P χ j a b W V - 1‖ ≤
      4 * (probeBadE (Ideal.absNorm P.asIdeal) a *
        probeBadT (Ideal.absNorm P.asIdeal) W) +
      8 * ((1 + probeBadE (Ideal.absNorm P.asIdeal) a) *
        (1 + probeBadT (Ideal.absNorm P.asIdeal) W) *
        probeBadA (Ideal.absNorm P.asIdeal) b) := by
  have hA0 : 0 ≤ probeBadA (Ideal.absNorm P.asIdeal) b := by
    unfold probeBadA; positivity
  have hE0 : 0 ≤ probeBadE (Ideal.absNorm P.asIdeal) a := by
    unfold probeBadE; positivity
  have hT0 : 0 ≤ probeBadT (Ideal.absNorm P.asIdeal) W := by
    unfold probeBadT; positivity
  have hAi : (1 - probeBadA (Ideal.absNorm P.asIdeal) b)⁻¹ ≤ 2 := by
    have hh : (1 / 2 : ℝ) ≤ 1 - probeBadA (Ideal.absNorm P.asIdeal) b := by linarith
    have hh' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hh
    simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using hh'
  have hVi : (1 - ‖V‖)⁻¹ ≤ 2 := by
    have hh : (1 / 2 : ℝ) ≤ 1 - ‖V‖ := by linarith
    have hh' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hh
    simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using hh'
  have hfirst := probeBadIdealFirst_norm_le K P χ hχ hminus j a b W V (by linarith)
  have htail := probeBadIdealTail_norm_le K P χ hχ hminus j a b W V (by linarith) (by linarith)
  have hf : ‖∑' m : ℕ, probeIdealSourceWeight K P χ j a b W V 1 0 1 m‖ ≤
      2 * (probeBadE (Ideal.absNorm P.asIdeal) a *
        probeBadT (Ideal.absNorm P.asIdeal) W) := by
    calc
      _ ≤ _ := hfirst
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hVi (mul_nonneg hE0 hT0) using 1
        ring
  have ht : ‖probeBadIdealTail K P χ j a b W V‖ ≤
      4 * ((1 + probeBadE (Ideal.absNorm P.asIdeal) a) *
        (1 + probeBadT (Ideal.absNorm P.asIdeal) W) *
        probeBadA (Ideal.absNorm P.asIdeal) b) := by
    calc
      _ ≤ _ := htail
      _ ≤ _ := by
        have hi := mul_le_mul hAi hVi (inv_nonneg.mpr (by linarith)) (by norm_num : (0 : ℝ) ≤ 2)
        have hC : 0 ≤ (1 + probeBadE (Ideal.absNorm P.asIdeal) a) *
            (1 + probeBadT (Ideal.absNorm P.asIdeal) W) *
            probeBadA (Ideal.absNorm P.asIdeal) b := by positivity
        convert mul_le_mul_of_nonneg_left hi hC using 1
        ring
  rw [probeBadIdealCorrection_sub_one K P χ hχ hminus j hj a b W V (by linarith) (by linarith), norm_mul]
  have hnorm : ‖1 - V‖ ≤ 2 := ArtinMatthews.probe_one_sub_norm_upper hV
  calc
    _ ≤ 2 * (‖∑' m : ℕ, probeIdealSourceWeight K P χ j a b W V 1 0 1 m‖ +
        ‖probeBadIdealTail K P χ j a b W V‖) :=
      mul_le_mul hnorm (norm_add_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ _ := by linarith

end
end ArtinMatthews.VaryingKummerAnalytic
