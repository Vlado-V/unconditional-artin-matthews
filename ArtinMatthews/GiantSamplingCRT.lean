module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! For the shifted product congruence, the first residue is a unit and
determines the second. The fixed character adds its two fixed modulus
coordinates without changing the number of moving residue classes. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem giantSampling_shiftedProduct_unit_iff {r a n : ℕ} :
    r ∣ a * n + 1 ↔ ∃ b : (ZMod r)ˣ,
      (a : ZMod r) = ↑b ∧ (n : ZMod r) = -(↑b⁻¹ : ZMod r) := by
  constructor
  · intro h
    have hzero := (ZMod.natCast_eq_zero_iff (a * n + 1) r).mpr h
    push_cast at hzero
    have hmul : (a : ZMod r) * (-(n : ZMod r)) = 1 := by
      rw [mul_neg]
      exact neg_eq_iff_add_eq_zero.mpr hzero
    let b := Units.mkOfMulEqOne (a : ZMod r) (-(n : ZMod r)) hmul
    refine ⟨b, rfl, ?_⟩
    change (n : ZMod r) = -(-(n : ZMod r))
    simp
  · rintro ⟨b, ha, hn⟩
    apply (ZMod.natCast_eq_zero_iff (a * n + 1) r).mp
    push_cast
    rw [ha, hn, mul_neg, Units.mul_inv, neg_add_cancel]

theorem giantSampling_shiftedProduct_unit_sum {A : Type*} [AddCommMonoid A]
    (r a n : ℕ) [NeZero r] (z : A) :
    (if r ∣ a * n + 1 then z else 0) =
      ∑ b : (ZMod r)ˣ,
        if (a : ZMod r) = ↑b ∧ (n : ZMod r) = -(↑b⁻¹ : ZMod r) then z else 0 := by
  classical
  by_cases hd : r ∣ a * n + 1
  · obtain ⟨b, hb⟩ := giantSampling_shiftedProduct_unit_iff.mp hd
    rw [ite_eq_left hd, Finset.sum_eq_single b]
    · exact (ite_eq_left hb).symm
    · intro c _hc hcb
      apply ite_eq_right
      intro h
      exact hcb (Units.ext (h.1.symm.trans hb.1))
    · intro hb'
      exact (hb' (Finset.mem_univ b)).elim
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro b _hb
    exact ite_eq_right (fun h => hd (giantSampling_shiftedProduct_unit_iff.mpr ⟨b, h⟩))

def giantSamplingLeftResidue {r M : ℕ}
    (b : (ZMod r)ˣ) (c : ZMod M) (z : ℂ) (a : ℕ) : ℂ :=
  if (a : ZMod r) = ↑b ∧ (a : ZMod M) = c then z else 0

def giantSamplingRightResidue {r M : ℕ}
    (b : (ZMod r)ˣ) (c : ZMod M) (n : ℕ) : ℂ :=
  if (n : ZMod r) = -(↑b⁻¹ : ZMod r) ∧ (n : ZMod M) = c then 1 else 0

theorem giantSampling_shiftedProduct_residue_expansion {r M : ℕ} [NeZero r] [NeZero M]
    (χ : DirichletCharacter ℂ M) (z : ℂ) (a n : ℕ) :
    (if r ∣ a * n + 1 then z * χ (a * n + 1) else 0) =
      ∑ c : (ZMod r)ˣ × ZMod M × ZMod M,
        χ (c.2.1 * c.2.2 + 1) * giantSamplingLeftResidue c.1 c.2.1 z a *
          giantSamplingRightResidue c.1 c.2.2 n := by
  classical
  rw [giantSampling_shiftedProduct_unit_sum, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases ha : (a : ZMod r) = ↑b
  · by_cases hn : (n : ZMod r) = -(↑b⁻¹ : ZMod r)
    · rw [ite_eq_left (And.intro ha hn), Finset.sum_eq_single (a : ZMod M)]
      · rw [Finset.sum_eq_single (n : ZMod M)]
        · simp only [giantSamplingLeftResidue, giantSamplingRightResidue, ha, hn,
            true_and, ite_true, mul_one]
          ring
        · intro c _hc hne
          simp [giantSamplingRightResidue, hne.symm]
        · intro h
          exact (h (Finset.mem_univ _)).elim
      · intro c _hc hne
        simp [giantSamplingLeftResidue, hne.symm]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · simp [giantSamplingRightResidue, hn]
  · simp [giantSamplingLeftResidue, ha]

theorem giantSampling_residue_card_le (r M : ℕ) [NeZero r] [NeZero M] :
    Fintype.card ((ZMod r)ˣ × ZMod M × ZMod M) ≤ r * M ^ 2 := by
  simp only [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card, pow_two]
  exact Nat.mul_le_mul_right _ (Nat.totient_le r)

end ArtinMatthews
