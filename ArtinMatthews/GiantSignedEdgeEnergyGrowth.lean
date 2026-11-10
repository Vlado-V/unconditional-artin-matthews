module

public import ArtinMatthews.GiantSignedEdgeStorePromote
public import ArtinMatthews.GiantSignedEdgeRowBound
public import ArtinMatthews.GiantSignedGhostMemoryMoments
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

/-! Exponential-domain convergence for the original unrestricted edge.
The growth base is used only for summability. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

omit [DecidableEq J] in
theorem giantSignedEdgeSquareTest_growth
    {B u v : ℝ} (hv : 0 < v)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (hf : ∀ target out, ‖f target out‖ ≤ B * u ^ (∑ j, out.1 j))
    (target : GiantSignedPrimeTuple P t) (out : GiantSignedMemory P) :
    ‖f target out‖ ^ 2 / v ^ (∑ j, out.1 j) ≤
      B ^ 2 * (max 1 (u ^ 2 / v)) ^ (∑ j, out.1 j) := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hf target out) 2
  calc
    _ ≤ (B * u ^ (∑ j, out.1 j)) ^ 2 / v ^ (∑ j, out.1 j) :=
      (div_le_div_iff_of_pos_right (pow_pos hv _)).mpr hs
    _ = B ^ 2 * (u ^ 2 / v) ^ (∑ j, out.1 j) := by
      rw [mul_pow, div_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (∑ j, out.1 j) 2]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg (sq_nonneg u) hv.le) (le_max_right _ _) _)
      (sq_nonneg B)

omit [DecidableEq J] in
theorem giantSignedEdgeSquareTest_symmetric
    (v : ℝ) (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (hf : ∀ target, GiantSignedMemorySymmetric (f target))
    (target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (σ : (j : J) → Equiv.Perm (Fin (m.1 j))) :
    ‖f target (giantSignedMemoryPermute m σ)‖ ^ 2 /
        v ^ (∑ j, (giantSignedMemoryPermute m σ).1 j) =
      ‖f target m‖ ^ 2 / v ^ (∑ j, m.1 j) := by
  rw [hf target m σ]
  rfl

variable [∀ j, ∀ p : P j, NeZero p.val]

theorem giantSignedEdgeApply_norm_summable
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) {vmin massMax ρ B u w : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ j, vmin ≤ V j)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hB : 0 ≤ B) (hu : 1 ≤ u) (hw : 0 ≤ w)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (hf : ∀ target out, ‖f target out‖ ≤ B * u ^ (∑ j, out.1 j))
    (source : GiantSignedPrimeTuple P t) :
    Summable (fun m : GiantSignedMemory P => giantSignedMemoryMass ν m *
      w ^ (∑ j, m.1 j) *
        ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source f m‖) := by
  let C := (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax tmax) ^ Fintype.card J
  have hs := (giantSignedMemory_exponential_summable ν hν (w * u)
    (mul_nonneg hw (le_trans zero_le_one hu))).mul_left (B * C)
  apply hs.of_nonneg_of_le
  · intro m
    exact mul_nonneg (mul_nonneg (giantSignedMemoryMass_nonneg ν hν m)
      (pow_nonneg hw _)) (norm_nonneg _)
  · intro m
    calc
      _ ≤ giantSignedMemoryMass ν m * w ^ (∑ j, m.1 j) *
          (B * u ^ (∑ j, m.1 j) * C) :=
        mul_le_mul_of_nonneg_left
          (giantSignedEdgeApply_row_bound ν hν V hvmin hV hMass hρ hρ1 hu hB
            tmax ht d D source f hf m)
          (mul_nonneg (giantSignedMemoryMass_nonneg ν hν m) (pow_nonneg hw _))
      _ = _ := by rw [mul_pow]; ring

end
end ArtinMatthews
