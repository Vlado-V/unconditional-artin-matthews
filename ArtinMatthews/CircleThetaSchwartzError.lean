module

public import ArtinMatthews.CircleThetaErrorRate
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

/-! A dilation-uniform detector error for the actual Schwartz source tests. -/

noncomputable section
namespace ArtinMatthews

theorem circleThetaSchwartzSourceError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ F r L : ℕ, 0 < F → 0 < r → F.Coprime r →
      4 * (F*r) ≤ L → ∀ (χ : OAI.SevenEighths.HeckeFamily.Character)
      (m1 m2 T1 T2 : ℕ), 0 < m1 → Squarefree m1 →
      ∀ (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ),
      circleThetaSourceError χ m1 m2 T1 T2 (fun x => W1 (x/K1)) (fun x => W2 (x/K2)) F r L ≤
        C * ((T1 : ℝ)*T2)^2 * (SchwartzMap.seminorm ℝ 0 0 W1) *
          (SchwartzMap.seminorm ℝ 0 0 W2) * (F : ℝ) * (r : ℝ) *
          (((m2 / m1.gcd m2)*T1 + (m1 / m1.gcd m2)*T2 : ℕ) : ℝ)^2 / Real.sqrt L := by
  obtain ⟨C, hC, hbound⟩ := circleThetaSourceError_bound
  refine ⟨C, hC, ?_⟩
  intro F r L hF hr hFr hL χ m1 m2 T1 T2 hm1 hsq W1 W2 K1 K2
  exact hbound F r L hF hr hFr hL χ m1 m2 T1 T2 hm1 hsq
    (fun x => W1 (x/K1)) (fun x => W2 (x/K2))
    (SchwartzMap.seminorm ℝ 0 0 W1) (SchwartzMap.seminorm ℝ 0 0 W2)
    (apply_nonneg _ _) (apply_nonneg _ _)
    (fun _ _ => SchwartzMap.norm_le_seminorm ℝ W1 _)
    (fun _ _ => SchwartzMap.norm_le_seminorm ℝ W2 _)

end ArtinMatthews
