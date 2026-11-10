module

public import ArtinMatthews.GiantSignedFockMoments
public import ArtinMatthews.GiantSignedGhostPointwise
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! The real positive row used by weighted Cauchy is the original ghost
formula evaluated at nonnegative coefficients. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedGhostPositiveApply {P : Finset ℕ} (ν : P → ℝ)
    (A C D : ℝ) (f : GiantSignedGroupMemory P → ℝ) (m : GiantSignedGroupMemory P) : ℝ :=
  ∑ S ∈ (giantSignedGhostZeroIndices m).powerset,
    D ^ S.card * A ^ ((giantSignedGhostZeroIndices m).card - S.card) *
      ∑' b : ℕ, (C ^ b / (Nat.factorial b : ℝ)) *
        ∑ β : Fin b → P, (∏ i, ν (β i)) * f (giantSignedGhostTarget m S β)

theorem giantSignedGhostPositiveApply_coe {P : Finset ℕ} (ν : P → ℝ)
    (A C D : ℝ) (f : GiantSignedGroupMemory P → ℝ) (m : GiantSignedGroupMemory P) :
    (giantSignedGhostPositiveApply ν A C D f m : ℂ) =
      giantSignedGhostGroupApply ν (A : ℂ) (C : ℂ) (D : ℂ) (fun t => (f t : ℂ)) m := by
  classical
  unfold giantSignedGhostPositiveApply giantSignedGhostGroupApply
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_tsum, Complex.ofReal_natCast, Complex.ofReal_prod]

theorem giantSignedGhostPositiveApply_nonneg {P : Finset ℕ} (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (A C D : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (f : GiantSignedGroupMemory P → ℝ) (hf : ∀ m, 0 ≤ f m) (m : GiantSignedGroupMemory P) :
    0 ≤ giantSignedGhostPositiveApply ν A C D f m := by
  unfold giantSignedGhostPositiveApply
  apply Finset.sum_nonneg
  intro S _
  apply mul_nonneg (mul_nonneg (pow_nonneg hD _) (pow_nonneg hA _))
  apply tsum_nonneg
  intro b
  apply mul_nonneg (div_nonneg (pow_nonneg hC _) (Nat.cast_nonneg _))
  exact Finset.sum_nonneg fun β _ =>
    mul_nonneg (Finset.prod_nonneg fun i _ => hν (β i)) (hf _)

theorem giantSignedGhostPositiveApply_weight {P : Finset ℕ} (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (A C D v : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hv : 0 < v)
    (hc : A + D / v ≤ 1) (m : GiantSignedGroupMemory P) :
    giantSignedGhostPositiveApply ν A C D (fun t => v ^ t.1) m ≤
      v ^ m.1 * Real.exp (C * (∑ p : P, ν p) * v) := by
  have h := giantSignedGhostGroupApply_weight_bound ν hν
    (A : ℂ) (C : ℂ) (D : ℂ) (fun t => ((v ^ t.1 : ℝ) : ℂ)) 1 v zero_le_one hv
    (by simpa only [Complex.norm_real, Real.norm_of_nonneg hA,
      Real.norm_of_nonneg hD] using hc)
    (fun t => by simp only [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hv.le _), one_mul, le_refl]) m
  rw [← giantSignedGhostPositiveApply_coe] at h
  simpa only [Complex.norm_real,
    Real.norm_of_nonneg (giantSignedGhostPositiveApply_nonneg ν hν A C D hA hC hD
      (fun t => v ^ t.1) (fun t => pow_nonneg hv.le _) m), one_mul,
    Real.norm_of_nonneg hC] using h

def giantSignedGhostCauchyTest {P : Finset ℕ} (f : GiantSignedGroupMemory P → ℂ)
    (v : ℝ) (m : GiantSignedGroupMemory P) : ℝ := ‖f m‖ ^ 2 / v ^ m.1

theorem giantSignedGhostCauchyTest_nonneg {P : Finset ℕ}
    (f : GiantSignedGroupMemory P → ℂ) (v : ℝ) (hv : 0 ≤ v) (m : GiantSignedGroupMemory P) :
    0 ≤ giantSignedGhostCauchyTest f v m :=
  div_nonneg (sq_nonneg _) (pow_nonneg hv _)

theorem giantSignedGhostCauchyTest_bound {P : Finset ℕ}
    (f : GiantSignedGroupMemory P → ℂ) (B u v : ℝ) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (m : GiantSignedGroupMemory P) :
    giantSignedGhostCauchyTest f v m ≤ B ^ 2 * (u ^ 2 / v) ^ m.1 := by
  unfold giantSignedGhostCauchyTest
  calc
    _ ≤ (B * u ^ m.1) ^ 2 / v ^ m.1 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf m) _) (pow_nonneg hv.le _)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm m.1 2, pow_mul, div_pow, mul_div_assoc]

theorem giantSignedGhostCauchyTest_symmetric {P : Finset ℕ}
    (f : GiantSignedGroupMemory P → ℂ) (v : ℝ) (hf : GiantSignedGroupSymmetric f) :
    GiantSignedGroupSymmetric (fun m => (giantSignedGhostCauchyTest f v m : ℂ)) := by
  intro n a σ
  simp only [giantSignedGhostCauchyTest, hf n a σ]

end
end ArtinMatthews
