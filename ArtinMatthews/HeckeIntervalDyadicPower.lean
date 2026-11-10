module

public import ArtinMatthews.HeckeIntervalCutoff
public import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadic
public import OAI.NumberTheory.DirichletL.PrimeLogProfile
public import ArtinMatthews.HeckeIntervalMellinUniform
public import ArtinMatthews.HeckePrimeLongParameters
public import ArtinMatthews.HeckePrimeZeroMaximum
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
public import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicScaled


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform power cancellation for the actual moving interval logarithmic
profile. The width loss is explicit and all Mellin norms are discharged. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths

theorem heckeInterval_dyadic_power (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, 2 ≤ k ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Real.log 2 →
      ∀ H : ℝ, 5 ≤ H → ∀ η : HeckeFamily.Character,
      η.residue ≠ 1 → (η.modulus.absNorm : ℝ) ≤ H →
      ∀ t : ℝ, |t| ≤ H^B → ∀ L ∈ Set.Icc (0 : ℝ) 1,
      ‖HeckePrimeDyadic.polynomial η
        (PrimeLogProfile.profile (heckeLogIntervalCutoff ε u v) L) H 0 t‖ ≤
        (C/ε^k)*H^(13/32 : ℝ) := by
  obtain ⟨Cd, hCd, hdirect⟩ := HeckePrimeDyadic.scaled_direct_bound
    (1/1024) (1/64) (2*(B+1)+4) (by norm_num) (by norm_num) (by norm_num) (by linarith)
  obtain ⟨n, htail⟩ := HeckeDyadic.uniform_external_tail_order (B+1) 1 (2+1/64) 0
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, hm₂⟩ := heckeInterval_mellin_uniform 0 2 2
  obtain ⟨Cn, hCn, hmn⟩ := heckeInterval_mellin_uniform 0 2 (n+2)
  refine ⟨Cd*C₂+Cd*Cn*(2 : ℝ)^n, by positivity, n+2, by omega, ?_⟩
  intro ε hε hε1 u v hu huv hv H hH η hη hmod t ht L hL
  have hH1 : 1 ≤ H := by linarith
  have hHp : 0 < H := by linarith
  have hbud := heckePrime_bin_height_budget hH hB ht
  have hsupp := heckeLogIntervalCutoff_uniform_support hε hε1 hu huv hv
  have hsmooth := heckeLogIntervalCutoff_smooth hε huv
  have hmax : HeckeDetectorZeros.zeroMaximum (fun _ : Unit => η) (fun _ => hη)
      (3*(0+1 : ℕ)*H^(B+1)) < (7/8 : ℝ)+2*(1/1024) := by
    have h := heckeZeroMaximum_le_seven_eighths (fun _ : Unit => η) (fun _ => hη)
      (3*(0+1 : ℕ)*H^(B+1))
    linarith
  have hb := hdirect (fun _ : Unit => η) (fun _ => hη) (H^(B+1)) (7/8) 0 hbud.1
    (by norm_num) (by norm_num) hmax ()
    (PrimeLogProfile.profile (heckeLogIntervalCutoff ε u v) L) 1 (2*Real.exp 1)
    (by norm_num) ((PrimeLogProfile.profile_support _ L).trans hsupp)
    (PrimeLogProfile.profile_smooth _ 1 (2*Real.exp 1) (by norm_num) hsupp hsmooth L)
    H 1 1 0 t (H^(B+1)/2) (C₂/ε^2) (Cn/ε^(n+2)) n
    (by linarith) hmod (by norm_num) (by norm_num) (by positivity)
    (by simpa using hbud.2.1) (by simpa using hbud.2.2) (by positivity) (by positivity)
    (hm₂ ε hε hε1 u v hu huv hv L hL _ (by norm_num))
    (fun σ hσ => hmn ε hε hε1 u v hu huv hv L hL σ
      ⟨by linarith [hσ.1], by simpa only [sub_zero] using hσ.2⟩)
  have htail' := htail H 1 0 hH1 (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, Real.rpow_zero, mul_one] at htail'
  norm_num only [Real.rpow_one, sub_zero, sub_self, add_zero,
    show ((7/8 : ℝ)-1/2+8*(1/1024))*1+1/64 = 51/128 by norm_num,
    show (2 : ℝ)*1+1/64 = 2+1/64 by ring] at hb
  have hwidth : C₂/ε^2 ≤ C₂/ε^(n+2) :=
    div_le_div_of_nonneg_left hC₂.le (pow_pos hε _) (pow_le_pow_of_le_one hε.le hε1 (by omega))
  have hpow : H^(51/128 : ℝ) ≤ H^(13/32 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num)
  have hpow1 : 1 ≤ H^(13/32 : ℝ) := Real.one_le_rpow hH1 (by norm_num)
  apply hb.trans
  calc
    _ ≤ Cd*(C₂/ε^(n+2))*H^(13/32 : ℝ)+Cd*(Cn/ε^(n+2))*(2 : ℝ)^n := by
      apply add_le_add
      · gcongr
      · calc
          _ = (Cd*(Cn/ε^(n+2)))*(H^(2+1/64)/(1+H^(B+1)/2)^n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ Cd*(C₂/ε^(n+2))*H^(13/32 : ℝ)+
        (Cd*(Cn/ε^(n+2))*(2 : ℝ)^n)*H^(13/32 : ℝ) := by
      exact add_le_add le_rfl (le_mul_of_one_le_right (by positivity) hpow1)
    _ = _ := by ring

end ArtinMatthews
