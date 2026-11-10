module

public import ArtinMatthews.GiantSignedSmallOmissions
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

/-! The actual omitted product contains ell labels per small group.
Its source exponent is uniform in the copy count and the chosen subsets. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem giantSignedSmallOmittedProduct_le {S : Type*} [Fintype S]
    {P : S → Finset ℕ} {M ell : ℕ} (a : MarkedPhysicalMarking P M)
    (U : GiantSignedSmallOmission S M ell) {Y : ℝ}
    (ha : ∀ g i, (a g i : ℝ) ≤ Y) :
    (giantSignedSmallOmittedProduct a U : ℝ) ≤ Y ^ (ell * Fintype.card S) := by
  have hg (g : S) : (∏ i ∈ (U g).1, (a g i : ℝ)) ≤ Y ^ ell := by
    calc
      _ ≤ ∏ _i ∈ (U g).1, Y :=
        prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => ha g i)
      _ = _ := by rw [prod_const, markedRawDeletionBatch_deleted_card]
  calc
    _ = ∏ g, ∏ i ∈ (U g).1, (a g i : ℝ) := by
      simp only [giantSignedSmallOmittedProduct, Nat.cast_prod]
    _ ≤ ∏ _g : S, Y ^ ell := prod_le_prod₀
      (fun _ _ => prod_nonneg fun _ _ => Nat.cast_nonneg _) (fun g _ => hg g)
    _ = _ := by rw [prod_const, card_univ, ← pow_mul]

theorem giantSignedSmallOmittedProduct_le_exp {S : Type*} [Fintype S]
    {P : S → Finset ℕ} {M ell : ℕ} (a : MarkedPhysicalMarking P M)
    (U : GiantSignedSmallOmission S M ell) (t : ℝ)
    (ha : ∀ g i, (a g i : ℝ) ≤ Real.exp t) :
    (giantSignedSmallOmittedProduct a U : ℝ) ≤
      Real.exp ((ell : ℝ) * (Fintype.card S : ℝ) * t) := by
  convert giantSignedSmallOmittedProduct_le a U ha using 1
  rw [← Real.exp_nat_mul, Nat.cast_mul]

theorem giantSignedSmallOmittedProduct_lt_prime {S : Type*} [Fintype S]
    {P : S → Finset ℕ} {M ell p : ℕ} (a : MarkedPhysicalMarking P M)
    (t q : ℝ) (ha : ∀ g i, (a g i : ℝ) ≤ Real.exp t)
    (hbudget : (ell : ℝ) * (Fintype.card S : ℝ) * t < q)
    (hp : Real.exp q ≤ (p : ℝ)) (U : GiantSignedSmallOmission S M ell) :
    giantSignedSmallOmittedProduct a U < p := by
  have h := (giantSignedSmallOmittedProduct_le_exp a U t ha).trans_lt
    ((Real.exp_lt_exp.mpr hbudget).trans_le hp)
  exact_mod_cast h

theorem giantSignedSmallOmission_budget_eventually (A : ℝ) (ell : ℕ)
    {b c : ℝ} (hbc : b < c) :
    ∀ᶠ L : ℝ in atTop, ∀ count : ℕ, (count : ℝ) ≤ A * Real.log L →
      (ell : ℝ) * (count : ℝ) * L ^ b < L ^ c := by
  have hlim := ((isLittleO_log_rpow_atTop (sub_pos.mpr hbc)).tendsto_div_nhds_zero).const_mul
    ((ell : ℝ) * A)
  simp only [mul_zero] at hlim
  have hlt := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt, eventually_gt_atTop (0 : ℝ)] with L hL hLpos
  intro count hcount
  have hden : 0 < L ^ (c - b) := Real.rpow_pos_of_pos hLpos _
  have hcoef : (ell : ℝ) * A * Real.log L < L ^ (c - b) := by
    apply (div_lt_one hden).mp
    simpa only [mul_div_assoc, mul_assoc] using hL
  have hmain := mul_lt_mul_of_pos_right hcoef (Real.rpow_pos_of_pos hLpos b)
  have hpow : L ^ (c - b) * L ^ b = L ^ c := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg ell))
    (Real.rpow_nonneg hLpos.le b)).trans_lt (by simpa only [mul_assoc, hpow] using hmain)

end
end ArtinMatthews
