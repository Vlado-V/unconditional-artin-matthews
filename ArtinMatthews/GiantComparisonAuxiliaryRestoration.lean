module

public import ArtinMatthews.GiantComparisonListRestoration
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

/-! The physical comparison error has a nonnegative row envelope with
the two actual ordered free-list weights. The auxiliary harmonic mass
remains outside each row sum. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell m N : ℕ} {C : J → Finset (Fin k)}

theorem giantComparisonUnmaskedAuxiliary_error
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (x : ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C)
    (hK : ∀ c b b', K (giantComparisonJoinLabels c b) (giantComparisonJoinLabels c b') aux = L b b' aux)
    {M : ℝ} (hM : 0 ≤ M) (hL : ∀ b b', ‖L b b' aux‖ ≤ M) :
    ‖(∑ a : GiantComparisonUnmaskedEdge P C ell N aux,
        giantComparisonUnmaskedSummand x q Ψ χ F G K a) -
      giantComparisonIndependentAuxiliarySum N x q Ψ χ F G L aux‖ ≤
      giantTwoSidedPatternAuxiliaryMass aux *
        ∑ w : ↥(Ioc 0 N),
          ‖giantComparisonPositionKernel x Ψ χ F G (giantTwoSidedPatternAuxiliaryProduct aux) w.val‖ *
          giantComparisonOrderedFreeWeight P C ell q w.val *
          giantComparisonOrderedFreeWeight P C ell q (w.val+giantTwoSidedPatternAuxiliaryProduct aux) *
          M*giantComparisonRestorationLoss aux q w.val (w.val+giantTwoSidedPatternAuxiliaryProduct aux) := by
  let U := ↥(Ioc 0 N)
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let μ := giantTwoSidedPatternAuxiliaryMass aux
  let B := giantTwoSidedPatternFreshMass P C ell
  let W := giantComparisonOrderedFreeWeight P C ell q
  let A := giantComparisonRestorationLoss aux q
  let H (w : ℕ) := giantComparisonPositionKernel x Ψ χ F G d w
  let R (w : ℕ) := giantComparisonRestoredPair L aux q w (w+d)
  let I (w : ℕ) := giantComparisonIndependentPair L aux q w (w+d)
  have hμ : 0 ≤ μ := giantTwoSidedPatternAuxiliaryMass_nonneg hV aux
  rw [giantComparisonUnmasked_sum_eq_separated x q Ψ χ F G K L aux hK]
  change ‖(μ:ℂ)*(∑ w : U, H w.val*((B^2:ℝ):ℂ)*R w.val) -
      (μ:ℂ)*(∑ w : U, H w.val*((B^2:ℝ):ℂ)*I w.val)‖ ≤
    μ*∑ w : U, ‖H w.val‖*W w.val*W (w.val+d)*M*A w.val (w.val+d)
  rw [← mul_sub,← Finset.sum_sub_distrib,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hμ]
  apply mul_le_mul_of_nonneg_left _ hμ
  calc
    _ ≤ ∑ w : U, ‖H w.val*((B^2:ℝ):ℂ)*R w.val - H w.val*((B^2:ℝ):ℂ)*I w.val‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro w _
      have he := giantComparisonRestoredPair_error hP hdis hV L aux w.val (w.val+d) hq hq1 hM hL
      calc
        _ = ‖H w.val‖*B^2*‖R w.val-I w.val‖ := by
          rw [← mul_sub,norm_mul,norm_mul,Complex.norm_real,
            Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        _ ≤ ‖H w.val‖*B^2*(M*A w.val (w.val+d)*giantComparisonIndependentDamping P C ell q w.val (w.val+d)*
            (Fintype.card (GiantComparisonFreeMarking P C ell w.val):ℝ)*
            (Fintype.card (GiantComparisonFreeMarking P C ell (w.val+d)):ℝ)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by
          simp only [W, B, giantComparisonOrderedFreeWeight, giantComparisonIndependentDamping]
          ring

end
end ArtinMatthews
