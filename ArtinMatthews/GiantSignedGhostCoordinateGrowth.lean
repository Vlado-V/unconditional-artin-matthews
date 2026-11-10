module

public import ArtinMatthews.GiantSignedGhostCoordinateApply
public import ArtinMatthews.GiantSignedGhostGrowth
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

/-! Each actual coordinate ghost preserves the common exponential class
on the complete finite product of pending memories. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}

theorem giantSignedGhostCoordinateApply_exponential
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (g : B) (f : GiantSignedMemoryGroups P → ℂ)
    (hf : GiantSignedGhostProductExponential f) :
    GiantSignedGhostProductExponential (giantSignedGhostCoordinateApply ν A C D g f) := by
  obtain ⟨Cf, u, hCf, hu, hf⟩ := hf
  let E := Real.exp (‖C g‖ * (∑ p : P g, ν g p) * u)
  let v := u * max 1 (‖A g‖ + ‖D g‖ / u)
  have hv : 0 < v := mul_pos hu (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have huv : u ≤ v := le_mul_of_one_le_right hu.le (le_max_left _ _)
  refine ⟨Cf * E, v, mul_nonneg hCf (Real.exp_nonneg _), hv, ?_⟩
  have hs (t : GiantSignedGroupMemory (P g))
      (y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h)) :
      ‖giantSignedGhostCoordinateApply ν A C D g f ((giantSignedMemorySplit P g).symm (t, y))‖ ≤
        (Cf * E) * v ^ giantSignedMemoryTotalDegree ((giantSignedMemorySplit P g).symm (t, y)) := by
    rw [giantSignedGhostCoordinateApply_split, giantSignedMemoryTotalDegree_split]
    let s := ∑ h : {h : B // h ≠ g}, (y h).1
    have hbase : 0 ≤ Cf * u ^ s := mul_nonneg hCf (pow_nonneg hu.le _)
    have hg := giantSignedGhostGroupApply_exponential_bound (ν g) (hν g) (A g) (C g) (D g)
      (fun r => f ((giantSignedMemorySplit P g).symm (r, y))) (Cf * u ^ s) u hbase hu
      (giantSignedGhostProduct_slice_bound f Cf u hf g y) t
    calc
      _ ≤ ((Cf * u ^ s) * E) * v ^ t.1 := hg
      _ = (Cf * E) * (u ^ s * v ^ t.1) := by ring
      _ ≤ (Cf * E) * (v ^ s * v ^ t.1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.le huv _) (pow_nonneg hv.le _))
          (mul_nonneg hCf (Real.exp_nonneg _))
      _ = _ := by rw [pow_add]; ring
  intro x
  simpa only [Prod.eta, Equiv.symm_apply_apply] using
    hs (giantSignedMemorySplit P g x).1 (giantSignedMemorySplit P g x).2

end
end ArtinMatthews
