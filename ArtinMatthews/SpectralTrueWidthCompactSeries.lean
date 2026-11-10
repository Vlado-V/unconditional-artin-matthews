module

public import ArtinMatthews.SpectralTrueWidthKloosterman
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! A compact spatial test supported in the positive line meets only
finitely many of the actual normalized true-width moduli. -/

namespace ArtinMatthews
open Set
open scoped MatrixGroups
noncomputable section

/-- For any fixed numerator, the test vanishes once the actual modulus
has passed a finite cutoff. -/
theorem gamma0TrueWidth_compactTest_zero_above (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (A : ℝ) (f : ℝ → ℂ) (hfc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ M : ℕ, ∀ c : Ioi (0 : ℕ), M ≤ c.val →
      f (A / gamma0TrueWidthModulus N r s (c.val : ℝ)) = 0 := by
  by_cases hne : (tsupport f).Nonempty
  · obtain ⟨ε, hε⟩ := hfc.exists_isLeast hne
    have hεpos : 0 < ε := hp hε.1
    let W := gamma0TrueWidthModulus N r s (1 : ℝ)
    have hW : 0 < W := gamma0TrueWidthModulus_pos N r s zero_lt_one
    obtain ⟨M, hM⟩ := exists_nat_gt (A / (ε * W))
    refine ⟨M, fun c hc => ?_⟩
    have hcR : (M : ℝ) ≤ (c.val : ℝ) := Nat.cast_le.mpr hc
    have hC : 0 < gamma0TrueWidthModulus N r s (c.val : ℝ) :=
      gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
    have hmod : gamma0TrueWidthModulus N r s (c.val : ℝ) = (c.val : ℝ) * W := by
      unfold W gamma0TrueWidthModulus
      ring
    have harg : A / gamma0TrueWidthModulus N r s (c.val : ℝ) < ε := by
      apply (div_lt_iff₀ hC).2
      rw [hmod]
      calc
        A < (c.val : ℝ) * (ε * W) :=
          (div_lt_iff₀ (mul_pos hεpos hW)).1 (hM.trans_le hcR)
        _ = ε * ((c.val : ℝ) * W) := by ring
    by_contra hnonzero
    exact (not_lt_of_ge (hε.2 (subset_tsupport f hnonzero))) harg
  · refine ⟨0, fun c _ => ?_⟩
    by_contra hnonzero
    exact hne ⟨_, subset_tsupport f hnonzero⟩

/-- The literal Kloosterman term with the exact true-width denominator
has finite support and an absolutely summable modulus series. -/
theorem gamma0TrueWidth_compactTest_summable (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (A : ℝ) (f : ℝ → ℂ)
    (hfc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    let G : Ioi (0 : ℕ) → ℂ := fun c =>
      letI : NeZero c.val := ⟨c.property.ne'⟩
      let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
      (gamma0TrueWidthKloostermanSum N r s c.val m n / (C : ℂ)) * f (A / C)
    (Function.support G).Finite ∧ Summable G ∧ Summable (fun c => ‖G c‖) := by
  intro G
  obtain ⟨M, hM⟩ := gamma0TrueWidth_compactTest_zero_above N r s A f hfc hp
  have hfinite : (Function.support G).Finite := by
    have hpre : ((Subtype.val : Ioi (0 : ℕ) → ℕ) ⁻¹' Iic M).Finite :=
      (finite_Iic M).preimage Subtype.val_injective.injOn
    refine hpre.subset fun c hc => ?_
    change c.val ≤ M
    by_contra hn
    change G c ≠ 0 at hc
    exact hc (by simp only [G, hM c (le_of_lt (lt_of_not_ge hn)), mul_zero])
  have hnorm : (Function.support (fun c => ‖G c‖)).Finite := by
    refine hfinite.subset fun c hc => ?_
    change ‖G c‖ ≠ 0 at hc
    change G c ≠ 0
    exact fun hzero => hc (by simp only [hzero, norm_zero])
  exact ⟨hfinite, summable_of_hasFiniteSupport hfinite, summable_of_hasFiniteSupport hnorm⟩

end
end ArtinMatthews
