module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Fourier.ZMod
public import OAI.NumberTheory.EgyptianFractions.CorrelationPhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.JointDickman.Amplification.AdditivePhaseBridge


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! # Finite Fourier expansion of character-twisted logarithmic sums -/
namespace JointDickman
open Finset Complex Problem337

noncomputable def characterFourierCoefficient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ZMod q) : ℂ :=
  (q:ℂ)⁻¹ * ZMod.dft (fun n => χ n) k

lemma characterFourierCoefficient_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ZMod q) :
    ‖characterFourierCoefficient χ k‖ ≤ 1 := by
  have hsum : ‖ZMod.dft (fun n => χ n) k‖ ≤ (q:ℝ) := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ n : ZMod q, ‖ZMod.stdAddChar (-(n*k)) • χ n‖ := norm_sum_le _ _
      _ ≤ ∑ _n : ZMod q, (1:ℝ) := by
        apply sum_le_sum
        intro n _
        simpa [smul_eq_mul,norm_mul,ZMod.stdAddChar_apply] using χ.norm_le_one n
      _ = q := by simp
  rw [characterFourierCoefficient,norm_mul,norm_inv,Complex.norm_natCast]
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hq.le)).trans_eq
    (inv_mul_cancel₀ hq.ne')

lemma character_fourier_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    χ n = ∑ k : ZMod q, characterFourierCoefficient χ k * ZMod.stdAddChar (k*n) := by
  have h := congrFun ((ZMod.dft (N := q) (E := ℂ)).symm_apply_apply (fun n => χ n)) n
  rw [ZMod.invDFT_apply] at h
  rw [←h,smul_eq_mul,mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [characterFourierCoefficient,smul_eq_mul]
  ring

lemma stdAddChar_mul_int_as_phase {q : ℕ} [NeZero q] (k : ZMod q) (n : ℤ) :
    ZMod.stdAddChar (k*(n:ZMod q)) =
      differencingPhase ((k.val:ℝ)/q*(n:ℝ)) := by
  conv_lhs => rw [←ZMod.natCast_zmod_val k]
  have he : (k.val:ZMod q)*(n:ZMod q) = ((k.val:ℤ)*n:ℤ) := by push_cast; rfl
  rw [he,ZMod.stdAddChar_coe]
  unfold differencingPhase
  congr 1
  push_cast
  ring

lemma differencingPhase_add (x y : ℝ) :
    differencingPhase (x+y) = differencingPhase x*differencingPhase y :=
  additivePhase_add x y

lemma character_log_sum_fourier {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset ℤ) (Z : ℝ) :
    (∑ n ∈ S, χ (n:ZMod q)*differencingPhase (Z*Real.log (n:ℝ))) =
      ∑ k : ZMod q, characterFourierCoefficient χ k *
        ∑ n ∈ S, differencingPhase ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ)) := by
  conv_lhs => arg 2; ext n; rw [character_fourier_expansion χ (n:ZMod q),sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  rw [stdAddChar_mul_int_as_phase,differencingPhase_add,mul_assoc]

lemma character_log_sum_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset ℤ) (Z K : ℝ) (_hK : 0 ≤ K)
    (hbound : ∀ a : ℝ, ‖∑ n ∈ S,
      differencingPhase (a*(n:ℝ)+Z*Real.log (n:ℝ))‖ ≤ K) :
    ‖∑ n ∈ S, χ (n:ZMod q)*differencingPhase (Z*Real.log (n:ℝ))‖ ≤ (q:ℝ)*K := by
  rw [character_log_sum_fourier]
  calc
    _ ≤ ∑ k : ZMod q, ‖characterFourierCoefficient χ k *
        ∑ n ∈ S, differencingPhase ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _k : ZMod q, K := by
      apply sum_le_sum
      intro k _
      rw [norm_mul]
      exact (mul_le_mul (characterFourierCoefficient_norm_le χ k)
        (hbound _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = (q:ℝ)*K := by simp

end JointDickman

end OAI
