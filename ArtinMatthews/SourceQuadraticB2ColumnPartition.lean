module

public import ArtinMatthews.SourceQuadraticShortColumns
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound


set_option backward.privateInPublic true
@[expose] public section

/-! Only the positive B2 energy is split into column dyads. The B3
blocks inside each dyad are kept with their actual real parts. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain QuadraticScale
open OAI.FiniteSieveOperator
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

def sourceQuadraticPoissonColumnDyad (n : ℕ) : ℕ := Nat.log 2 (n - 1)

theorem sourceQuadraticPoissonColumnDyad_upper {n j : ℕ} (hn : 0 < n)
    (hj : sourceQuadraticPoissonColumnDyad n = j) : (n : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n - 1)
  rw [← sourceQuadraticPoissonColumnDyad, hj] at h
  have hle : n ≤ (2 : ℕ) ^ j.succ := by omega
  have hreal : (n : ℝ) ≤ (2 : ℝ) ^ j.succ := by exact_mod_cast hle
  simpa only [Nat.succ_eq_add_one, pow_succ, mul_comm] using hreal

theorem sourceQuadraticPoissonColumnDyad_lower {n j : ℕ} (hj0 : j ≠ 0)
    (hj : sourceQuadraticPoissonColumnDyad n = j) : (2 : ℝ) ^ j < (n : ℝ) := by
  have hn : n - 1 ≠ 0 := by
    intro h
    apply hj0
    simpa only [sourceQuadraticPoissonColumnDyad, h, Nat.log_zero_right] using hj.symm
  have h := Nat.pow_log_le_self 2 hn
  rw [← sourceQuadraticPoissonColumnDyad, hj] at h
  have hlt : (2 : ℕ) ^ j < n := by omega
  exact_mod_cast hlt

theorem sourceQuadraticB2Energy_column_partition_le (rows cols : Finset E) (w : E → ℝ)
    (hw : ∀ d ∈ rows, 0 ≤ w d) (I : Finset ℕ) (index : E → ℕ)
    (hi : ∀ e ∈ cols, index e ∈ I) (a : E → ℂ) :
    sourceQuadraticB2Energy F S₀ hζ rows cols w a ≤ (I.card : ℝ) *
      ∑ j ∈ I, sourceQuadraticB2Energy F S₀ hζ rows (cols.filter fun e => index e = j) w a := by
  let block (j : ℕ) := cols.filter (fun e => index e = j)
  have hrow (d : E) : ‖rowValue cols χ a d‖ ^ 2 ≤
      I.card * ∑ j ∈ I, ‖rowValue (block j) χ a d‖ ^ 2 := by
    have hs : rowValue cols χ a d = ∑ j ∈ I, rowValue (block j) χ a d :=
      (Finset.sum_fiberwise_of_maps_to hi (fun e => χ d e * a e)).symm
    rw [hs]
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
    simpa using Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ))
      (fun j => ‖rowValue (block j) χ a d‖)
  unfold sourceQuadraticB2Energy
  calc
    _ ≤ ∑ d ∈ rows, w d * ((I.card : ℝ) * ∑ j ∈ I, ‖rowValue (block j) χ a d‖ ^ 2) :=
      Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hrow d) (hw d hd))
    _ = (I.card : ℝ) * ∑ d ∈ rows, ∑ j ∈ I, w d * ‖rowValue (block j) χ a d‖ ^ 2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [Finset.sum_comm]

theorem sourceQuadraticB2Energy_crude (rows cols : Finset E) (w : E → ℝ)
    (hw : ∀ d ∈ rows, w d ≤ 1) (a : E → ℂ) :
    sourceQuadraticB2Energy F S₀ hζ rows cols w a ≤
      ((rows.card : ℝ) * cols.card) * coeffMass cols a := by
  refine (show sourceQuadraticB2Energy F S₀ hζ rows cols w a ≤
    finiteEnergy rows cols χ a from ?_).trans ?_
  · exact Finset.sum_le_sum (fun d hd => mul_le_of_le_one_left (sq_nonneg _) (hw d hd))
  · exact isEnergyBound_card rows cols χ
      (fun d _ c _ => sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ d c) a

theorem sourceQuadraticB2Norm_le_of_energy (rows : Finset E) (w : E → ℝ) (N : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (h : IsEnergyBound rows (sourceQuadraticB2Columns F S₀ N)
      (fun d c => (Real.sqrt (w d) : ℂ) * χ d c) B) :
    sourceQuadraticB2Norm F S₀ hζ rows w N ≤ B := by
  let cols := sourceQuadraticB2Columns F S₀ N
  apply squared_norm_le_of_energy _ _ hB
  intro a
  let v (c : E) : ℂ := if hc : c ∈ cols then a ⟨c, hc⟩ else 0
  have hv (c : cols) : v c.val = a c := dite_eq_left c.property
  have hs := h v
  unfold finiteEnergy rowValue coeffMass at hs
  rw [← Finset.sum_coe_sort rows
    (fun d => ‖∑ c ∈ cols, ((Real.sqrt (w d) : ℂ) * χ d c) * v c‖ ^ 2),
    ← Finset.sum_coe_sort cols (fun c => ‖v c‖ ^ 2)] at hs
  simp_rw [← Finset.sum_coe_sort cols
    (fun c => ((Real.sqrt (w _) : ℂ) * χ _ c) * v c), hv] at hs
  exact hs

theorem sourceQuadraticB2Norm_le_of_weighted_energy
    (rows : Finset E) (w : E → ℝ) (N : ℝ) (hw : ∀ d ∈ rows, 0 ≤ w d)
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a : E → ℂ, sourceQuadraticB2Energy F S₀ hζ rows (sourceQuadraticB2Columns F S₀ N) w a ≤
      B * coeffMass (sourceQuadraticB2Columns F S₀ N) a) :
    sourceQuadraticB2Norm F S₀ hζ rows w N ≤ B := by
  apply sourceQuadraticB2Norm_le_of_energy F S₀ hζ rows w N hB
  intro a
  refine (show finiteEnergy rows (sourceQuadraticB2Columns F S₀ N)
    (fun d c => (Real.sqrt (w d) : ℂ) * χ d c) a =
      sourceQuadraticB2Energy F S₀ hζ rows (sourceQuadraticB2Columns F S₀ N) w a from ?_).le.trans
      (h a)
  unfold finiteEnergy sourceQuadraticB2Energy rowValue
  apply Finset.sum_congr rfl
  intro d hd
  have he : (∑ c ∈ sourceQuadraticB2Columns F S₀ N, ((Real.sqrt (w d) : ℂ) * χ d c) * a c) =
      (Real.sqrt (w d) : ℂ) * ∑ c ∈ sourceQuadraticB2Columns F S₀ N, χ d c * a c := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [he, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hw d hd)]

end
end ArtinMatthews.SourceEulerAssembly
