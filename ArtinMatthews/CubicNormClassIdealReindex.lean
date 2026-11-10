module

public import ArtinMatthews.CubicNormCellGeometry
public import ArtinMatthews.CubicNormClassResidues
public import ArtinMatthews.CubicThetaLattice
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The finite ideal norm-class test has the exact six-unit lattice
normalization. Its genuine shifted cutoff and Dirichlet twist are retained. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def giantCubicNormClassSum (η : HeckeFamily.Character) {M q : ℕ}
    (χ : DirichletCharacter ℂ M) (b : ZMod q) (Φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 * x + 1⌋₊,
    if (n : ZMod q) = b then
      idealThetaCoeff η n * χ n * (Φ (((n : ℝ) - 1) / x) : ℂ)
    else 0

theorem cubicNormCoordinate_absNorm (z : ℤ × ℤ) :
    eisensteinIntegerNorm z = ((Ideal.span {thetaCoordinateEquiv z}).absNorm : ℤ) := by
  have h := theta_normForm_eq_absNorm_span z
  simp only [EisensteinTheta.normForm] at h
  exact_mod_cast h

private theorem cubicNorm_shifted_cutoff_mem (Φ : ℝ → ℝ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x)
    {n : ℕ} (hn : Φ (((n : ℝ) - 1) / x) ≠ 0) :
    n ∈ Finset.Icc 1 ⌊2 * x + 1⌋₊ := by
  have hx₀ := zero_lt_one.trans_le hx
  obtain ⟨hlo, hhi⟩ := hs hn
  have h₁ := (lt_div_iff₀ hx₀).mp hlo
  have h₂ := (div_lt_iff₀ hx₀).mp hhi
  have hn₁ : (1 : ℝ) ≤ n := by linarith
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hn₁, Nat.le_floor (by linarith)⟩

theorem giantCubicNormClassSum_six_eq_lattice (η : HeckeFamily.Character) {M q : ℕ}
    (χ : DirichletCharacter ℂ M) (b : ZMod q) (Φ : ℝ → ℝ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x) :
    6 * giantCubicNormClassSum η χ b Φ x =
      ∑' z : ℤ × ℤ, cubicNormClassWeight η χ b z * (cubicNormRadial Φ x z : ℂ) := by
  classical
  let S := Finset.Icc 1 ⌊2 * x + 1⌋₊
  let g (n : ℕ) : ℂ := if (n : ZMod q) = b then χ n * (Φ (((n : ℝ) - 1) / x) : ℂ) else 0
  let f (z : HeckeFamily.O) : ℂ :=
    thetaIdealCharacter η (Ideal.span {z}) * g (Ideal.span {z}).absNorm
  have hg (n : ℕ) (hn : n ∉ S) : g n = 0 := by
    have hzero : Φ (((n : ℝ) - 1) / x) = 0 :=
      not_not.mp (fun h => hn (cubicNorm_shifted_cutoff_mem Φ hs hx h))
    simp [g, hzero]
  have hzero : f 0 = 0 := by
    dsimp only [f]
    rw [Ideal.span_singleton_zero]
    change thetaIdealCharacter η 0 * _ = _
    rw [map_zero, zero_mul]
  have hunit (u : HeckeFamily.Oˣ) (z : HeckeFamily.O) : f (u.val * z) = f z := by
    simp only [f, Ideal.span_singleton_mul_left_unit u.isUnit]
  have hcoord (z : ℤ × ℤ) : f (thetaCoordinateEquiv z) =
      cubicNormClassWeight η χ b z * (cubicNormRadial Φ x z : ℂ) := by
    have hnorm := cubicNormCoordinate_absNorm z
    rw [cubicNormClassWeight, cubicNormRadial, hnorm]
    simp only [Int.cast_natCast]
    by_cases hz : thetaCoordinateEquiv z = 0
    · have hΦ₀ : Φ (-(1 : ℝ) / x) = 0 := by
        by_contra h
        have hh := (lt_div_iff₀ (zero_lt_one.trans_le hx)).mp (hs h).1
        linarith
      rw [hz, hzero]
      have hnorm₀ : (Ideal.span ({0} : Set HeckeFamily.O)).absNorm = 0 :=
        Ideal.absNorm_eq_zero_iff.mpr (Ideal.span_singleton_eq_bot.mpr rfl)
      simp only [hnorm₀, Nat.cast_zero, zero_sub, hΦ₀, Complex.ofReal_zero, mul_zero]
    · dsimp only [f]
      rw [thetaIdealCharacter_span η hz]
      change HeckeFamily.elementCoeff η (HeckeFamily.coordinateElement z.1 z.2) * _ = _
      dsimp only [g]
      split_ifs <;> ring
  have hf : Summable f := by
    apply thetaCoordinateEquiv.summable_iff.mp
    apply summable_of_ne_finset_zero (s := cubicNormCoordinateBox ⌊3 * Real.sqrt x⌋₊)
    intro z hz
    change f (thetaCoordinateEquiv z) = 0
    rw [hcoord]
    have hradial : cubicNormRadial Φ x z = 0 :=
      not_not.mp (fun h => hz (cubicNormRadial_mem_coordinateBox Φ hs hx h))
    rw [hradial, Complex.ofReal_zero, mul_zero]
  have hgen (I : UnrestrictedIdealReindex.NonzeroIdeal) :
      f (ConcretePrimeRowBridge.idealGenerator I.val) = thetaIdealCharacter η I.val * g I.val.absNorm := by
    simp only [f, ConcretePrimeRowBridge.span_idealGenerator]
  have hnz :
      (∑' I : UnrestrictedIdealReindex.NonzeroIdeal, thetaIdealCharacter η I.val * g I.val.absNorm) =
        ∑' I : Ideal HeckeFamily.O, thetaIdealCharacter η I * g I.absNorm := by
    apply tsum_subtype_eq_of_support_subset
      (f := fun I : Ideal HeckeFamily.O => thetaIdealCharacter η I * g I.absNorm)
      (s := {I : Ideal HeckeFamily.O | I ≠ 0})
    intro I hI h
    exact hI (by simp only [h, thetaIdealCharacter_zero, zero_mul])
  let U := S.biUnion idealsOfNorm
  have hU (I : Ideal HeckeFamily.O) (hI : I ∉ U) : thetaIdealCharacter η I * g I.absNorm = 0 := by
    have hnorm : I.absNorm ∉ S :=
      fun h => hI (Finset.mem_biUnion.mpr ⟨I.absNorm, h, mem_idealsOfNorm.mpr rfl⟩)
    rw [hg _ hnorm, mul_zero]
  have hsum :
      (∑' I : Ideal HeckeFamily.O, thetaIdealCharacter η I * g I.absNorm) =
        giantCubicNormClassSum η χ b Φ x := by
    rw [tsum_eq_sum (s := U) hU]
    dsimp only [U]
    rw [Finset.sum_biUnion]
    · unfold giantCubicNormClassSum
      apply Finset.sum_congr rfl
      intro n _hn
      have hrow : (∑ I ∈ idealsOfNorm n, thetaIdealCharacter η I * g I.absNorm) =
          idealThetaCoeff η n * g n := by
        simp only [idealThetaCoeff, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro I hI
        rw [mem_idealsOfNorm.mp hI]
      rw [hrow]
      dsimp only [g]
      split_ifs <;> ring
    · intro n _hn m _hm hne
      apply Finset.disjoint_left.mpr
      intro I hi hj
      exact hne ((mem_idealsOfNorm.mp hi).symm.trans (mem_idealsOfNorm.mp hj))
  have hunitSum := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero f hf hzero hunit
  simp_rw [hgen] at hunitSum
  rw [hnz, hsum] at hunitSum
  rw [← hunitSum, ← thetaCoordinateEquiv.tsum_eq]
  exact tsum_congr hcoord

end ArtinMatthews
