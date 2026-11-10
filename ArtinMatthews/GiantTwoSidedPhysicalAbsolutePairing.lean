module

public import ArtinMatthews.GiantTwoSidedPhysicalFamilyMatrix
public import ArtinMatthews.GiantTwoSidedPatternSlotAverage
public import ArtinMatthews.MarkedPhysicalEndpointNorm
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

/-! The literal absolute physical form takes the norm of each original
choice before the finite pattern, permutation and auxiliary sums. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    {k ell : ℕ} {Z : Finset ℕ}

def giantTwoSidedPhysicalFamilyAbsoluteEntry
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (s t : GiantTwoSidedEndpointState P (k+ell) Z) : ℝ :=
  ∑ p ∈ patterns, giantTwoSidedSlotAverage (giantTwoSidedPatternAbsoluteEntry step q ζ (K p)) s t

theorem giantTwoSidedPhysicalFamilyAbsoluteEntry_expand
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (s t : GiantTwoSidedEndpointState P (k+ell) Z) :
    giantTwoSidedPhysicalFamilyAbsoluteEntry patterns C step q ζ K s t =
      ∑ choice : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell,
        giantTwoSidedResidueSlotNormalization (J := J) (k+ell) *
          ‖giantTwoSidedPhysicalChoiceCoefficient step q ζ K choice s t‖ := by
  let Permutations := J → Equiv.Perm (Fin (k+ell))
  have hsum : (∑ choice : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell,
      ‖giantTwoSidedPhysicalChoiceCoefficient step q ζ K choice s t‖) =
      ∑ p ∈ patterns, ∑ π : Permutations, ∑ τ : Permutations,
        ∑ aux : GiantTwoSidedPatternAuxiliary P (C p),
          ‖giantTwoSidedPatternPhysicalCoefficient step q ζ (K p)
            (giantTwoSidedEndpointPermute π s) (giantTwoSidedEndpointPermute τ t) aux‖ := by
    rw [Fintype.sum_sigma, ← sum_coe_sort patterns]
    apply sum_congr rfl
    intro p _
    simp only [Fintype.sum_prod_type, giantTwoSidedPhysicalChoiceCoefficient]
    rfl
  rw [← mul_sum, hsum]
  unfold giantTwoSidedPhysicalFamilyAbsoluteEntry giantTwoSidedSlotAverage
    giantTwoSidedPatternAbsoluteEntry giantTwoSidedResidueSlotNormalization
  rw [← sum_div, div_eq_mul_inv, mul_comm]

theorem giantTwoSidedPhysicalFamilyAbsoluteEntry_nonneg
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (s t : GiantTwoSidedEndpointState P (k+ell) Z) :
    0 ≤ giantTwoSidedPhysicalFamilyAbsoluteEntry patterns C step q ζ K s t := by
  rw [giantTwoSidedPhysicalFamilyAbsoluteEntry_expand]
  exact sum_nonneg fun c _ => mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (norm_nonneg _)

def giantTwoSidedPhysicalFamilyAbsolutePairing
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) : ℝ :=
  ∑ c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell,
    ∑ s : GiantTwoSidedEndpointState P (k+ell) Z, ∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
      ‖(markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) *
        (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ) *
        giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t * star (f s.val.1.val) * g t‖

theorem giantTwoSidedPhysicalFamilyAbsolutePairing_eq_entries
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalFamilyAbsolutePairing patterns C step q ζ K f g =
      ∑ s : GiantTwoSidedEndpointState P (k+ell) Z, ∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
        markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) *
          giantTwoSidedPhysicalFamilyAbsoluteEntry patterns C step q ζ K s t * ‖f s.val.1.val‖ * ‖g t‖ := by
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let Choice := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell
  let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
  let a := giantTwoSidedResidueSlotNormalization (J := J) (k+ell)
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _ (fun _ => sum_nonneg (fun _ _ => by positivity))
  have ha : 0 ≤ a := inv_nonneg.mpr (sq_nonneg _)
  let F (c : Choice) (s t : State) :=
    σ * a * ‖giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t‖ * ‖f s.val.1.val‖ * ‖g t‖
  have hswap (s : State) : (∑ t : State, ∑ c : Choice, F c s t) =
      ∑ c : Choice, ∑ t : State, F c s t := sum_comm
  have hsum : (∑ s : State, ∑ t : State, ∑ c : Choice, F c s t) =
      ∑ c : Choice, ∑ s : State, ∑ t : State, F c s t := by
    simp only [hswap]
    exact sum_comm
  calc
    _ = ∑ c : Choice, ∑ s : State, ∑ t : State, F c s t := by
      change (∑ c : Choice, ∑ s : State, ∑ t : State,
        ‖(σ : ℂ) * (a : ℂ) * giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t *
          star (f s.val.1.val) * g t‖) = _
      simp only [F, norm_mul, norm_star, Complex.norm_real,
        Real.norm_of_nonneg hσ, Real.norm_of_nonneg ha]
    _ = ∑ s : State, ∑ t : State, ∑ c : Choice, F c s t := hsum.symm
    _ = _ := by
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro t _
      rw [giantTwoSidedPhysicalFamilyAbsoluteEntry_expand]
      simp only [mul_sum, sum_mul]
      apply sum_congr rfl
      intro c _
      dsimp only [F, σ, a]
      ring

end
end ArtinMatthews
