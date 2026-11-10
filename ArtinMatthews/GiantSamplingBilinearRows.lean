module

public import ArtinMatthews.GiantSamplingSquareRows
public import ArtinMatthews.GiantSamplingCRT
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact squarefree row in the large-factor term is a finite sum of
the literal source tests of Proposition 5.1. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def giantCubicSamplingBilinear (η : HeckeFamily.Character)
    (Φ : ℝ → ℝ) (x : ℝ) (A N : Finset ℕ) (α β : ℕ → ℂ) : ℂ :=
  ∑ a ∈ A, ∑ n ∈ N, α a * β n *
    (Φ (((a * n : ℕ) : ℝ) / x) : ℂ) * idealThetaCoeff η (a * n + 1)

theorem giantCubicSamplingSquareRow_eq_crt (η : HeckeFamily.Character)
    {M r : ℕ} [NeZero M] [NeZero r]
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ)
    (K : Finset ℕ) (B d : ℕ) :
    let A := giantSamplingSquarefreeRow K B d
    let N := giantSamplingScaledWindow x ε d
    (∑ a ∈ A, ∑ n ∈ N, H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (a * n)) =
      ∑ c : (ZMod r)ˣ × ZMod M × ZMod M, χ (c.2.1 * c.2.2 + 1) *
        giantCubicSamplingBilinear η Φ x A N
          (fun a => giantSamplingLeftResidue c.1 c.2.1 (H (d ^ 2 * a)) a)
          (giantSamplingRightResidue c.1 c.2.2) := by
  classical
  let A := giantSamplingSquarefreeRow K B d
  let N := giantSamplingScaledWindow x ε d
  let R := (ZMod r)ˣ × ZMod M × ZMod M
  let α (c : R) (a : ℕ) := giantSamplingLeftResidue c.1 c.2.1 (H (d ^ 2 * a)) a
  let β (c : R) (n : ℕ) := giantSamplingRightResidue c.1 c.2.2 n
  let w (a n : ℕ) :=
    (Φ (((a * n : ℕ) : ℝ) / x) : ℂ) * idealThetaCoeff η (a * n + 1)
  have hpoint (a n : ℕ) :
      H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (a * n) =
        ∑ c : R, χ (c.2.1 * c.2.2 + 1) * (α c a * β c n * w a n) := by
    calc
      _ = (if r ∣ a * n + 1 then H (d ^ 2 * a) * χ (a * n + 1) else 0) * w a n := by
        unfold giantCubicSamplingKernel
        dsimp only [w]
        split_ifs
        · simp only [Nat.cast_mul]
          ring
        · simp
      _ = _ := by
        rw [giantSampling_shiftedProduct_residue_expansion, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _hc
        dsimp only [α, β]
        ring
  unfold giantCubicSamplingBilinear
  change (∑ a ∈ A, ∑ n ∈ N,
      H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (a * n)) =
    ∑ c : R, χ (c.2.1 * c.2.2 + 1) *
      ∑ a ∈ A, ∑ n ∈ N, α c a * β c n *
        (Φ (((a * n : ℕ) : ℝ) / x) : ℂ) * idealThetaCoeff η (a * n + 1)
  simp_rw [hpoint, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := N) (t := (Finset.univ : Finset R))]
  rw [Finset.sum_comm (s := A) (t := (Finset.univ : Finset R))]
  simp only [w, mul_assoc]

end ArtinMatthews
