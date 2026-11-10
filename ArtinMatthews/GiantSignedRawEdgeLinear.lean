module

public import ArtinMatthews.GiantSignedRawEdgeSplit
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

/-! Finite linearity and the literal clean/dirty split of the original
raw edge family. No restriction is placed on the old memory degree. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B I : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

section Single
variable {C : B → Finset (Fin k)}

theorem giantSignedRawEdgeApply_add (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (f g : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K η (fun t => f t + g t) s =
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s +
        giantSignedRawEdgeApply ν V κ q ρ θ ζ K η g s := by
  unfold giantSignedRawEdgeApply
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem giantSignedRawEdgeApply_sub (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (f g : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K η (fun t => f t - g t) s =
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s -
        giantSignedRawEdgeApply ν V κ q ρ θ ζ K η g s := by
  unfold giantSignedRawEdgeApply
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem giantSignedRawEdgeApply_mul (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (c : ℂ) (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K η (fun t => c * f t) s =
      c * giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s := by
  unfold giantSignedRawEdgeApply
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem giantSignedRawEdgeApply_zero (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K η (fun _ => 0) s = 0 := by
  simp only [giantSignedRawEdgeApply, mul_zero, Finset.sum_const_zero]

theorem giantSignedRawEdgeApply_multiplier_add (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η ξ : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeApply ν V κ q ρ θ ζ K (fun s r => η s r + ξ s r) f s =
      giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s +
        giantSignedRawEdgeApply ν V κ q ρ θ ζ K ξ f s := by
  unfold giantSignedRawEdgeApply
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end Single

section Family

theorem giantSignedRawEdgeFamilyApply_add (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f g : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η (fun t => f t + g t) s =
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f s +
        giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η g s := by
  simp only [giantSignedRawEdgeFamilyApply, giantSignedRawEdgeApply_add, Finset.sum_add_distrib]

theorem giantSignedRawEdgeFamilyApply_sub (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f g : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η (fun t => f t - g t) s =
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f s -
        giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η g s := by
  simp only [giantSignedRawEdgeFamilyApply, giantSignedRawEdgeApply_sub, Finset.sum_sub_distrib]

theorem giantSignedRawEdgeFamilyApply_zero (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η (fun _ => 0) s = 0 := by
  simp only [giantSignedRawEdgeFamilyApply, giantSignedRawEdgeApply_zero, Finset.sum_const_zero]

theorem giantSignedRawEdgeFamilyApply_clean_add_dirty (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f s =
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K
        (fun i s r => η i s r * giantSignedRawEdgeCleanMultiplier s r) f s +
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K
        (fun i s r => η i s r * giantSignedRawEdgeDirtyMultiplier s r) f s := by
  unfold giantSignedRawEdgeFamilyApply
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => giantSignedRawEdgeApply_clean_add_dirty
    ν V κ q ρ θ ζ (K i) (η i) f s)

end Family
end
end ArtinMatthews
