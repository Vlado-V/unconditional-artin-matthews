module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovOrthogonality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
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
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseGram


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Finite Fourier Bessel inequality on the coefficient torus, for the
localized kernel in the double mean-value estimate. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped ComplexConjugate Classical

noncomputable def halaszCharacterL2 {k : ℕ} (m : Fin k → ℤ) :
    Lp ℂ 2 (halaszVinogradovHaar k) :=
  ContinuousMap.toLp 2 (halaszVinogradovHaar k) ℂ
    ⟨halaszVinogradovCharacter m,halasz_vinogradov_character_continuous m⟩

lemma halasz_character_l2_coe {k : ℕ} (m : Fin k → ℤ) :
    (halaszCharacterL2 m : (Fin k → AddCircle (1:ℝ)) → ℂ) =ᵐ[halaszVinogradovHaar k]
      halaszVinogradovCharacter m :=
  ContinuousMap.coeFn_toAEEqFun (halaszVinogradovHaar k)
    ⟨halaszVinogradovCharacter m,halasz_vinogradov_character_continuous m⟩

lemma halasz_character_l2_inner {k : ℕ} (m n : Fin k → ℤ) :
    inner ℂ (halaszCharacterL2 m) (halaszCharacterL2 n) = if m=n then 1 else 0 := by
  rw [L2.inner_def]
  have hh : (∫ α, inner ℂ (halaszCharacterL2 m α) (halaszCharacterL2 n α)
      ∂halaszVinogradovHaar k) =
      ∫ α, halaszVinogradovCharacter n α*conj (halaszVinogradovCharacter m α)
        ∂halaszVinogradovHaar k := by
    apply integral_congr_ae
    filter_upwards [halasz_character_l2_coe m,halasz_character_l2_coe n] with α hm hn
    rw [hm,hn]
    simp only [RCLike.inner_apply',mul_comm]
  rw [hh,halasz_vinogradov_character_inner]
  simp only [eq_comm]

theorem halasz_torus_bessel {k : ℕ} (S : Finset (Fin k → ℤ))
    (U : (Fin k → AddCircle (1:ℝ)) → ℂ) (hU : MemLp U 2 (halaszVinogradovHaar k)) :
    (∑ m∈S, ‖∫ α, conj (halaszVinogradovCharacter m α)*U α
      ∂halaszVinogradovHaar k‖^2) ≤
      ∫ α, ‖U α‖^2 ∂halaszVinogradovHaar k := by
  let u := hU.toLp U
  have heval (m : Fin k → ℤ) : inner ℂ (halaszCharacterL2 m) u =
      ∫ α, conj (halaszVinogradovCharacter m α)*U α ∂halaszVinogradovHaar k := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [halasz_character_l2_coe m,hU.coeFn_toLp] with α hm hu
    change (halaszCharacterL2 m α)=_ at hm
    change u α=U α at hu
    rw [hm,hu]
    simp only [RCLike.inner_apply']
  have hnorm : ‖u‖^2=∫ α, ‖U α‖^2 ∂halaszVinogradovHaar k := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re (L2.integrable_inner u u)]
    apply integral_congr_ae
    filter_upwards [hU.coeFn_toLp] with α hu
    change u α=U α at hu
    rw [hu]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (U α)).symm
  have hh := mrt_gram_analysis S halaszCharacterL2 u (B := 1) (by norm_num)
    (fun m hm => by
      simp only [halasz_character_l2_inner,apply_ite norm,norm_one,norm_zero]
      simp [hm])
  simpa only [heval,hnorm,one_mul] using hh

end TwoPointCorrelations

end OAI
