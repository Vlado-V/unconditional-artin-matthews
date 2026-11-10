module

public import ArtinMatthews.QuadraticHeckeRayDualTail
public import ArtinMatthews.QuadraticHeckeSquarefreeNorm
public import ArtinMatthews.QuadraticHeckeRayDualAbsoluteTail
public import ArtinMatthews.QuadraticHeckeSquarefreeNormBound
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
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

/-- The genuine character-weighted dual profile has a uniform squarefree-part absolute tail. -/
theorem quadraticHeckeRayDualTerm_squarefree_absolute_tail_bound
    (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (hc : HasCompactSupport w)
    (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {u σ : ℝ} (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c U : ℝ), 0 < c → 0 < U →
      ∀ {m : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F m),
      (∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then
        ‖quadraticHeckeRayDualTerm F ψ A r w c J‖ else 0) ≤
          C * c ^ (-σ) * U ^ (u - σ) := by
  obtain ⟨C, hC, hbound⟩ :=
    quadraticHeckeRayDualTerm_absolute_tail_bound F A r w hc hp hs hu huσ
  refine ⟨C, hC, ?_⟩
  intro c U hc' hU m ψ
  exact (quadraticHeckeSquarefreeNorm_absolute_tail_le F
    (fun J => ‖quadraticHeckeRayDualTerm F ψ A r w c J‖)
    (fun _ => norm_nonneg _)
    (quadraticHeckeRayDualTerm_norm_summable F ψ A r w hc hp hs hc') U).trans
      (hbound c U hc' hU ψ)

/-- The signed squarefree-part tail has the same bound with no summability hypothesis. -/
theorem quadraticHeckeRayDualTerm_squarefree_tail_bound
    (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (hc : HasCompactSupport w)
    (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {u σ : ℝ} (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c U : ℝ), 0 < c → 0 < U →
      ∀ {m : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F m),
      ‖∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then
        quadraticHeckeRayDualTerm F ψ A r w c J else 0‖ ≤
          C * c ^ (-σ) * U ^ (u - σ) := by
  obtain ⟨C, hC, hbound⟩ :=
    quadraticHeckeRayDualTerm_absolute_tail_bound F A r w hc hp hs hu huσ
  refine ⟨C, hC, ?_⟩
  intro c U hc' hU m ψ
  exact (quadraticHeckeSquarefreeNorm_tail_norm_le F
    (quadraticHeckeRayDualTerm F ψ A r w c)
    (quadraticHeckeRayDualTerm_norm_summable F ψ A r w hc hp hs hc') U).trans
      (hbound c U hc' hU ψ)

end
end ArtinMatthews
