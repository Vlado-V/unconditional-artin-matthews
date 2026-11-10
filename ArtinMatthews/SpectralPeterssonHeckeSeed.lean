module

public import ArtinMatthews.SpectralPeterssonPoincare
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import ArtinMatthews.SpectralFourierBruhatKernel
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal real height regulator for weight two. For a positive
parameter the original cusp-row sum is absolutely convergent. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

def spectralPeterssonHeckeSeed (u : ℝ) (m : ℕ+) (z : UpperHalfPlane) : ℂ :=
  ((z.im^u : ℝ) : ℂ)*spectralHolomorphicCuspSeed (m : ℕ) z

theorem spectralPeterssonHeckeSeed_zero (m : ℕ+) :
    spectralPeterssonHeckeSeed 0 m = spectralHolomorphicCuspSeed (m : ℕ) := by
  funext z
  simp [spectralPeterssonHeckeSeed]

theorem spectralPeterssonHeckeSeed_slash_translation (u : ℝ) (m : ℕ+) (l : ℤ) :
    spectralHolomorphicSlash 2 (realTranslation (l : ℝ)) (spectralPeterssonHeckeSeed u m) =
      spectralPeterssonHeckeSeed u m := by
  funext z
  rw [spectralHolomorphicSlash_apply]
  have hdenom : ((((realTranslation (l : ℝ)) 1 0 : ℝ) : ℂ)*(z : ℂ)+
      (((realTranslation (l : ℝ)) 1 1 : ℝ) : ℂ)) = 1 := by simp [realTranslation]
  rw [hdenom,one_pow,div_one]
  have h := congrFun (spectralHolomorphicCuspSeed_slash_translation 2 (m : ℕ) l) z
  rw [spectralHolomorphicSlash_apply,hdenom,one_pow,div_one] at h
  unfold spectralPeterssonHeckeSeed
  rw [realTranslation_im_smul,h]

theorem spectralPeterssonHecke_im (G : SL(2, ℝ)) (z : UpperHalfPlane) :
    (G • z).im = z.im/‖((G 1 0 : ℝ) : ℂ)*(z : ℂ)+((G 1 1 : ℝ) : ℂ)‖^2 := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ G • z).im = _
  rw [UpperHalfPlane.im_smul_eq_div_normSq,Matrix.SpecialLinearGroup.det_mapGL,
    Units.val_one,abs_one,one_mul,Complex.normSq_eq_norm_sq]
  simp [UpperHalfPlane.denom]

theorem spectralPeterssonHeckeSlash_norm (u : ℝ) (m : ℕ+) (G : SL(2, ℝ)) (z : UpperHalfPlane) :
    ‖spectralHolomorphicSlash 2 G (spectralPeterssonHeckeSeed u m) z‖ =
      z.im^u * ‖((G 1 0 : ℝ) : ℂ)*(z : ℂ)+((G 1 1 : ℝ) : ℂ)‖^(-(2+2*u)) *
        Real.exp (-(2*Real.pi*(m : ℝ)*(G • z).im)) := by
  let D := ((G 1 0 : ℝ) : ℂ)*(z : ℂ)+((G 1 1 : ℝ) : ℂ)
  have hD : 0 < ‖D‖ := by
    rw [norm_pos_iff]
    have h := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ G) z
    simpa [UpperHalfPlane.denom,D] using h
  rw [spectralHolomorphicSlash_apply]
  unfold spectralPeterssonHeckeSeed
  simp only [norm_div,norm_pow,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (G • z).im_pos.le _),spectralHolomorphicCuspSeed_norm]
  change ((G • z).im^u * Real.exp (-(2*Real.pi*(m : ℝ)*(G • z).im)))/‖D‖^2 = _
  have he : ((G • z).im^u) = z.im^u/(‖D‖^(2*u)) := by
    rw [spectralPeterssonHecke_im]
    change (z.im/‖D‖^2)^u = _
    rw [Real.div_rpow z.im_pos.le (by positivity),← Real.rpow_natCast_mul hD.le 2 u]
    norm_num
  rw [he,Real.rpow_neg hD.le,Real.rpow_add hD,Real.rpow_two]
  simp only [_root_.mul_inv_rev,div_eq_mul_inv]
  ring

def gamma0PeterssonHeckeMatrixSeed (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (M : SL(2, ℤ)) : UpperHalfPlane → ℂ :=
  spectralHolomorphicSlash 2 (gamma0TrueWidthMatrix N b a M) (spectralPeterssonHeckeSeed u m)

def gamma0PeterssonHeckeSignedSummand (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (p : Gamma0PeterssonSignedRow N b a) : UpperHalfPlane → ℂ :=
  gamma0PeterssonHeckeMatrixSeed N b a u m (gamma0PeterssonRowMatrix N b a p).val

theorem gamma0PeterssonHeckeSignedSummand_of_matrix (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (M : gamma0CuspCorrespondence N b a) :
    gamma0PeterssonHeckeSignedSummand N b a u m (gamma0PeterssonRowOfMatrix N b a M) =
      gamma0PeterssonHeckeMatrixSeed N b a u m M.val := by
  let p := gamma0PeterssonRowOfMatrix N b a M
  let R := gamma0PeterssonRowMatrix N b a p
  have hp := gamma0PeterssonRowMatrix_row N b a p
  obtain ⟨l,hl⟩ := gamma0Petersson_left_translate_of_row_eq N b a M R (congrFun hp 0) (congrFun hp 1)
  change gamma0PeterssonHeckeMatrixSeed N b a u m R.val = _
  unfold gamma0PeterssonHeckeMatrixSeed
  rw [hl,gamma0Petersson_normalized_left_translate,spectralHolomorphicSlash_mul,
    spectralPeterssonHeckeSeed_slash_translation]

theorem gamma0PeterssonHeckeSignedSummand_norm_le (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (hu : 0 < u) (m : ℕ+) (p : Gamma0PeterssonSignedRow N b a) (z : UpperHalfPlane) :
    ‖gamma0PeterssonHeckeSignedSummand N b a u m p z‖ ≤
      (z.im^u * (gamma0PeterssonWidthRatio N b a)^(-(2+2*u)) *
        (EisensteinSeries.r (gamma0PeterssonWidthDilation N b • z))^(-(2+2*u))) * ‖p.val‖^(-(2+2*u)) := by
  let M := (gamma0PeterssonRowMatrix N b a p).val
  let g := gamma0TrueWidthMatrix N b a M
  let w := gamma0PeterssonWidthRatio N b a
  let y := gamma0PeterssonWidthDilation N b • z
  let v := 2+2*u
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hrow := gamma0PeterssonRowMatrix_row N b a p
  have hw : 0 < w := gamma0PeterssonWidthRatio_pos N b a
  change ‖spectralHolomorphicSlash 2 g (spectralPeterssonHeckeSeed u m) z‖ ≤
    (z.im^u*w^(-v)*(EisensteinSeries.r y)^(-v))*‖p.val‖^(-v)
  rw [spectralPeterssonHeckeSlash_norm]
  have he := gamma0Petersson_normalized_denom N b a M z
  change ((g 1 0 : ℝ) : ℂ)*(z : ℂ)+((g 1 1 : ℝ) : ℂ) =
    (w : ℂ)*((M 1 0 : ℂ)*(y : ℂ)+(M 1 1 : ℂ)) at he
  rw [he,show M 1 0 = p.val 0 from congrFun hrow 0,show M 1 1 = p.val 1 from congrFun hrow 1,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.le,Real.mul_rpow hw.le (norm_nonneg _)]
  have hexp : Real.exp (-(2*Real.pi*(m : ℝ)*(g • z).im)) ≤ 1 :=
    spectralHolomorphicCuspSeed_norm (m : ℕ) (g • z) ▸
      spectralHolomorphicCuspSeed_norm_le_one (m : ℕ) (g • z)
  calc
    _ ≤ z.im^u*(w^(-v)*‖(p.val 0 : ℂ)*(y : ℂ)+(p.val 1 : ℂ)‖^(-v))*1 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ _ := by
      rw [mul_one,← mul_assoc,mul_assoc (z.im^u*w^(-v))]
      exact mul_le_mul_of_nonneg_left (EisensteinSeries.summand_bound y hv p.val) (by positivity)

theorem gamma0PeterssonHeckeSignedSummand_summable (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (hu : 0 < u) (m : ℕ+) (z : UpperHalfPlane) :
    Summable (fun p : Gamma0PeterssonSignedRow N b a => ‖gamma0PeterssonHeckeSignedSummand N b a u m p z‖) := by
  have h := (EisensteinSeries.summable_one_div_norm_rpow (by linarith : 2 < 2+2*u)).subtype
    {p : Fin 2 → ℤ | ∃ M : gamma0CuspCorrespondence N b a, (fun i => M.val 1 i) = p}
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p =>
    gamma0PeterssonHeckeSignedSummand_norm_le N b a u hu m p z) (h.mul_left _)

def gamma0PeterssonHeckeChart (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (z : UpperHalfPlane) : ℂ :=
  (1/2 : ℂ)*(∑' p : Gamma0PeterssonSignedRow N b a, gamma0PeterssonHeckeSignedSummand N b a u m p z)

def gamma0PeterssonHecke (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) : UpperHalfPlane → ℂ :=
  gamma0PeterssonHeckeChart N 1 a u m

end ArtinMatthews
