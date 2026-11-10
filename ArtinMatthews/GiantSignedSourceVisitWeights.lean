module

public import Mathlib.Analysis.Real.Sqrt
public import ArtinMatthews.GiantSignedGhostWeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The original endpoint visits use sqrt q and interior visits use q.
One memory weight is chosen before the word length and all group carriers. -/
namespace ArtinMatthews
noncomputable section

def giantSignedSourceVisitQ (q : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val = 0 ∨ i.val = n then Real.sqrt q else q

theorem giantSignedSourceVisitQ_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ giantSignedSourceVisitQ q n i ∧ giantSignedSourceVisitQ q n i ≤ Real.sqrt q := by
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq0
  have hs1 : Real.sqrt q ≤ 1 := by nlinarith
  have hqs : q ≤ Real.sqrt q := by nlinarith
  unfold giantSignedSourceVisitQ
  split_ifs
  · exact ⟨hs0, le_rfl⟩
  · exact ⟨hq0, hqs⟩

theorem giantSignedSourceGhostWeight_exists {q ρ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ ^ 2)
    (Vmax : ℝ) :
    ∃ v : ℝ, 1 < v ∧ ∀ qi Vg : ℝ, 0 ≤ qi → qi ≤ Real.sqrt q →
      0 ≤ Vg → Vg ≤ Vmax →
      |qi / ρ ^ 2| + |-(1-qi) / ρ| / v < 1 ∧
      |qi / ρ ^ 2| + 2 * |-(1-qi) * Vg / ρ| / v < 1 := by
  obtain ⟨v, hv, h⟩ := giantSignedGhostWeight_exists
    (Real.sqrt q / ρ ^ 2) (Vmax / ρ) (1 / ρ)
    (giantSignedGhost_source_A_lt_one hρ hgap)
  refine ⟨v, hv, ?_⟩
  intro qi Vg hqi0 hqis hVg0 hVgmax
  have hs2 := Real.sq_sqrt hq0
  have hs0 := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := by nlinarith
  have hqi1 : qi ≤ 1 := hqis.trans hs1
  have hA0 : 0 ≤ qi / ρ ^ 2 := div_nonneg hqi0 (sq_nonneg ρ)
  have hA : qi / ρ ^ 2 ≤ Real.sqrt q / ρ ^ 2 :=
    div_le_div_of_nonneg_right hqis (sq_nonneg ρ)
  have hC : |-(1-qi) * Vg / ρ| ≤ Vmax / ρ := by
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hqi1),
      abs_of_nonneg hVg0, abs_of_pos hρ]
    apply div_le_div_of_nonneg_right _ hρ.le
    exact (mul_le_of_le_one_left hVg0 (by linarith : 1 - qi ≤ 1)).trans hVgmax
  have hD : |-(1-qi) / ρ| ≤ 1 / ρ := by
    rw [abs_div, abs_neg, abs_of_nonneg (sub_nonneg.mpr hqi1), abs_of_pos hρ]
    exact div_le_div_of_nonneg_right (by linarith) hρ.le
  simpa only [abs_of_nonneg hA0] using
    h (qi / ρ ^ 2) (-(1-qi) * Vg / ρ) (-(1-qi) / ρ) hA hC hD

theorem giantSignedSourceVisitWeights_exists {q ρ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ ^ 2)
    (Vmax : ℝ) :
    ∃ v : ℝ, 1 < v ∧ ∀ (n : ℕ) (i : Fin (n + 1)) (Vg : ℝ),
      0 ≤ Vg → Vg ≤ Vmax →
      |giantSignedSourceVisitQ q n i / ρ ^ 2| +
        |-(1-giantSignedSourceVisitQ q n i) / ρ| / v < 1 ∧
      |giantSignedSourceVisitQ q n i / ρ ^ 2| +
        2 * |-(1-giantSignedSourceVisitQ q n i) * Vg / ρ| / v < 1 := by
  obtain ⟨v, hv, h⟩ := giantSignedSourceGhostWeight_exists hq0 hq1 hρ hgap Vmax
  refine ⟨v, hv, ?_⟩
  intro n i Vg hVg0 hVgmax
  exact h _ Vg (giantSignedSourceVisitQ_bounds hq0 hq1 n i).1
    (giantSignedSourceVisitQ_bounds hq0 hq1 n i).2 hVg0 hVgmax

end
end ArtinMatthews
