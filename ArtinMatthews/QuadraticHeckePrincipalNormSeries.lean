module

public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesClasses
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

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem quadraticHeckePrincipalIdeal_countable :
    Countable {I : Ideal (𝓞 F) // I ≠ ⊥} := by
  let : Countable (Ideal (𝓞 F)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  infer_instance

theorem quadraticHeckePrincipalIdealNorm_pos (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    0 < (Ideal.absNorm I.val : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h => I.property (Ideal.absNorm_eq_zero_iff.mp h))

private theorem quadraticHeckePrincipalIdealNorm_equiv (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    (FractionalIdeal.absNorm ((integralFractionalIdealsEquiv F) I).val.val : ℝ) =
      (Ideal.absNorm I.val : ℝ) := by
  change (FractionalIdeal.absNorm (I.val : FractionalIdeal (𝓞 F)⁰ F) : ℝ) = _
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]

theorem quadraticHeckePrincipalIdealNorm_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => (Ideal.absNorm I.val : ℝ) ^ (-σ)) := by
  apply ((integralFractionalIdeals_norm_summable (K := F) hσ).comp_injective
    (integralFractionalIdealsEquiv F).injective).congr
  intro I
  dsimp only [Function.comp_def]
  rw [quadraticHeckePrincipalIdealNorm_equiv]

theorem quadraticHeckePrincipalIdealSeries_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, ((Ideal.absNorm I.val : ℝ) : ℂ) ^ (-s)) =
      dedekindZeta F s := by
  rw [← integralDedekindDirichlet_eq_dedekindZeta F hs, integralDedekindDirichlet,
    ← (integralFractionalIdealsEquiv F).tsum_eq]
  apply tsum_congr
  intro I
  rw [quadraticHeckePrincipalIdealNorm_equiv]

end
end ArtinMatthews
