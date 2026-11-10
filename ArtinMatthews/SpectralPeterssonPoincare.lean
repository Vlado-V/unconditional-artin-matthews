module

public import ArtinMatthews.SpectralHolomorphicCuspSeed
public import ArtinMatthews.SpectralPeterssonCuspRows
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The native holomorphic Poincare series at a true-width cusp. Its
summands are independent of the left-translation representatives, and
the original positive projective row sum is absolutely convergent. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonWidthDilation (N : ℕ) [NeZero N] (b : SL(2, ℤ)) : SL(2, ℝ) :=
  cuspWidthDilation (gamma0CuspTrueWidth N b : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N b)

def gamma0PeterssonWidthRatio (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) : ℝ :=
  Real.sqrt (gamma0CuspTrueWidth N a : ℝ)/Real.sqrt (gamma0CuspTrueWidth N b : ℝ)

theorem gamma0PeterssonWidthRatio_pos (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) :
    0 < gamma0PeterssonWidthRatio N b a :=
  div_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)))
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)))

theorem gamma0Petersson_normalized_denom (N : ℕ) [NeZero N]
    (b a M : SL(2, ℤ)) (z : UpperHalfPlane) :
    ((gamma0TrueWidthMatrix N b a M 1 0 : ℝ) : ℂ)*(z : ℂ)+
      ((gamma0TrueWidthMatrix N b a M 1 1 : ℝ) : ℂ) =
    (gamma0PeterssonWidthRatio N b a : ℂ)*
      ((M 1 0 : ℂ)*((gamma0PeterssonWidthDilation N b • z : UpperHalfPlane) : ℂ)+(M 1 1 : ℂ)) := by
  obtain ⟨_,hC,hD⟩ := gamma0TrueWidthMatrix_entries N b a M
  rw [hC,hD]
  unfold gamma0PeterssonWidthRatio gamma0PeterssonWidthDilation
  rw [cuspWidthDilation_coe_smul]
  push_cast
  have hb : 0 < (gamma0CuspTrueWidth N b : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
  have hs : ((Real.sqrt (gamma0CuspTrueWidth N b : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  have hsq : ((Real.sqrt (gamma0CuspTrueWidth N b : ℝ) : ℝ) : ℂ)^2 =
      (gamma0CuspTrueWidth N b : ℂ) := by exact_mod_cast Real.sq_sqrt hb.le
  field_simp [hs]
  linear_combination (M 1 0 : ℂ)*(z : ℂ)*((Real.sqrt (gamma0CuspTrueWidth N a : ℝ) : ℝ) : ℂ)*hsq

def gamma0PeterssonMatrixSeed (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (M : SL(2, ℤ)) : UpperHalfPlane → ℂ :=
  spectralHolomorphicSlash k (gamma0TrueWidthMatrix N b a M) (spectralHolomorphicCuspSeed m)

theorem gamma0PeterssonMatrixSeed_of_row_eq (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (M R : gamma0CuspCorrespondence N b a)
    (hc : R.val 1 0 = M.val 1 0) (hd : R.val 1 1 = M.val 1 1) :
    gamma0PeterssonMatrixSeed N b a k m R.val = gamma0PeterssonMatrixSeed N b a k m M.val := by
  obtain ⟨l,hl⟩ := gamma0Petersson_left_translate_of_row_eq N b a M R hc hd
  unfold gamma0PeterssonMatrixSeed
  rw [hl,gamma0Petersson_normalized_left_translate,spectralHolomorphicSlash_mul,
    spectralHolomorphicCuspSeed_slash_translation]

def gamma0PeterssonSignedSummand (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (k m : ℕ)
    (p : Gamma0PeterssonSignedRow N b a) : UpperHalfPlane → ℂ :=
  gamma0PeterssonMatrixSeed N b a k m (gamma0PeterssonRowMatrix N b a p).val

theorem gamma0PeterssonSignedSummand_of_matrix (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (M : gamma0CuspCorrespondence N b a) :
    gamma0PeterssonSignedSummand N b a k m (gamma0PeterssonRowOfMatrix N b a M) =
      gamma0PeterssonMatrixSeed N b a k m M.val := by
  unfold gamma0PeterssonSignedSummand
  have hp := gamma0PeterssonRowMatrix_row N b a (gamma0PeterssonRowOfMatrix N b a M)
  exact gamma0PeterssonMatrixSeed_of_row_eq N b a k m M _ (congrFun hp 0) (congrFun hp 1)

theorem gamma0PeterssonSignedSummand_neg (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (hk : Even k) (p : Gamma0PeterssonSignedRow N b a) :
    gamma0PeterssonSignedSummand N b a k m (gamma0PeterssonSignedRowNeg N b a p) =
      gamma0PeterssonSignedSummand N b a k m p := by
  let M := gamma0PeterssonRowMatrix N b a p
  let R := gamma0CuspCorrespondenceNeg N b a M
  have hp : gamma0PeterssonSignedRowNeg N b a p = gamma0PeterssonRowOfMatrix N b a R := by
    apply Subtype.ext
    funext i
    have hi := congrFun (gamma0PeterssonRowMatrix_row N b a p) i
    change -p.val i = ((-M.val : SL(2, ℤ)) 1 i)
    simp [M,hi]
  rw [hp,gamma0PeterssonSignedSummand_of_matrix]
  change gamma0PeterssonMatrixSeed N b a k m (-M.val) =
    gamma0PeterssonMatrixSeed N b a k m M.val
  unfold gamma0PeterssonMatrixSeed
  rw [gamma0Petersson_normalized_neg,spectralHolomorphicSlash_neg k hk]

theorem gamma0PeterssonSignedSummand_norm_le (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (p : Gamma0PeterssonSignedRow N b a) (z : UpperHalfPlane) :
    ‖gamma0PeterssonSignedSummand N b a k m p z‖ ≤
      ((gamma0PeterssonWidthRatio N b a)^k)⁻¹*
        ‖EisensteinSeries.eisSummand (k : ℤ) p.val (gamma0PeterssonWidthDilation N b • z)‖ := by
  let M := (gamma0PeterssonRowMatrix N b a p).val
  let g := gamma0TrueWidthMatrix N b a M
  let w := gamma0PeterssonWidthRatio N b a
  let y := gamma0PeterssonWidthDilation N b • z
  have hrow := gamma0PeterssonRowMatrix_row N b a p
  change ‖spectralHolomorphicSlash k g (spectralHolomorphicCuspSeed m) z‖ ≤
    (w^k)⁻¹*‖EisensteinSeries.eisSummand (k : ℤ) p.val y‖
  rw [spectralHolomorphicSlash_apply,norm_div,norm_pow]
  have he := gamma0Petersson_normalized_denom N b a M z
  change ((g 1 0 : ℝ) : ℂ)*(z : ℂ)+((g 1 1 : ℝ) : ℂ) =
    (w : ℂ)*((M 1 0 : ℂ)*(y : ℂ)+(M 1 1 : ℂ)) at he
  rw [he,show M 1 0 = p.val 0 from congrFun hrow 0,show M 1 1 = p.val 1 from congrFun hrow 1,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg (gamma0PeterssonWidthRatio_pos N b a).le,mul_pow]
  unfold EisensteinSeries.eisSummand
  rw [norm_zpow,_root_.zpow_neg,zpow_natCast]
  calc
    _ ≤ 1/(w^k*‖(p.val 0 : ℂ)*(y : ℂ)+(p.val 1 : ℂ)‖^k) :=
      div_le_div_of_nonneg_right (spectralHolomorphicCuspSeed_norm_le_one m (g • z))
        (mul_nonneg (pow_nonneg (gamma0PeterssonWidthRatio_pos N b a).le _)
          (pow_nonneg (norm_nonneg _) _))
    _ = _ := by rw [one_div,_root_.mul_inv_rev,mul_comm]

theorem gamma0PeterssonSignedSummand_summable (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (hk : 3 ≤ k) (z : UpperHalfPlane) :
    Summable (fun p : Gamma0PeterssonSignedRow N b a => ‖gamma0PeterssonSignedSummand N b a k m p z‖) := by
  have h : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hs := (EisensteinSeries.summable_norm_eisSummand h (gamma0PeterssonWidthDilation N b • z)).subtype
    {p : Fin 2 → ℤ | ∃ M : gamma0CuspCorrespondence N b a, (fun i => M.val 1 i) = p}
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p =>
    gamma0PeterssonSignedSummand_norm_le N b a k m p z)
    (hs.mul_left ((gamma0PeterssonWidthRatio N b a)^k)⁻¹)

def gamma0PeterssonRowPositive {N : ℕ} {b a : SL(2, ℤ)} (p : Gamma0PeterssonSignedRow N b a) : Prop :=
  0 < p.val 0 ∨ p.val 0 = 0 ∧ 0 < p.val 1

def Gamma0PeterssonPositiveRow (N : ℕ) (b a : SL(2, ℤ)) :=
  {p : Gamma0PeterssonSignedRow N b a // gamma0PeterssonRowPositive p}

def gamma0PeterssonPoincareChart (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (k m : ℕ)
    (z : UpperHalfPlane) : ℂ :=
  ∑' p : Gamma0PeterssonPositiveRow N b a, gamma0PeterssonSignedSummand N b a k m p.val z

def gamma0PeterssonPoincare (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (k m : ℕ) :
    UpperHalfPlane → ℂ :=
  gamma0PeterssonPoincareChart N 1 a k m

theorem gamma0PeterssonPoincareChart_summable (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (hk : 3 ≤ k) (z : UpperHalfPlane) :
    Summable (fun p : Gamma0PeterssonPositiveRow N b a =>
      ‖gamma0PeterssonSignedSummand N b a k m p.val z‖) :=
  (gamma0PeterssonSignedSummand_summable N b a k m hk z).subtype {p | gamma0PeterssonRowPositive p}

end ArtinMatthews
