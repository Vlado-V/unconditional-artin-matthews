module

public import ArtinMatthews.GiantTwoSidedPhysicalMellinPairing
public import ArtinMatthews.IdealResidualFamily
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
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual physical cutoff pairing separates into its raw member
and every signed comparison member with both slot averages retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell : ℕ} {Z : Finset ℕ}

def giantTwoSidedPhysicalPatternCutoffPairing (C : J → Finset (Fin k))
    (step : ℤ) (q ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ)*
    (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ)*
      ∑ π : J → Equiv.Perm (Fin (k+ell)),
      ∑ τ : J → Equiv.Perm (Fin (k+ell)),
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,
      ∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
      ∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
        giantTwoSidedPatternPhysicalCoefficient step q ζ K
          (giantTwoSidedEndpointPermute π s) (giantTwoSidedEndpointPermute τ t) aux *
          (Ψ ((s.val.1.val : ℝ) /
            (x * (giantTwoSidedPatternDilation C (giantTwoSidedEndpointPermute π s).val.2 aux : ℝ))) /
            (s.val.1.val : ℂ)) * star (f s.val.1.val) * g t

theorem giantTwoSidedPhysicalCutoffPairing_sum_patterns {I : Type*}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x f g =
      ∑ p ∈ patterns, giantTwoSidedPhysicalPatternCutoffPairing (C p) step q ζ (K p) Ψ x f g := by
  unfold giantTwoSidedPhysicalCutoffPairing
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, giantTwoSidedPhysicalChoiceCoefficient,
    giantTwoSidedPhysicalChoiceDilation]
  rw [← sum_coe_sort patterns]
  simp only [giantTwoSidedPhysicalPatternCutoffPairing, mul_sum]

theorem giantTwoSidedPhysicalCutoffPairing_residual_expansion
    (probes₁ probes₂ : Finset (J × Fin k)) (step : ℤ) (q ζ : ℝ)
    (Q : ℕ) (h ξ : ℝ) (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
      idealResidualCopied step q ζ (idealResidualCoefficient P Q h ξ) Ψ x f g =
      giantTwoSidedPhysicalPatternCutoffPairing
        (idealResidualCopied (none : IdealResidualPattern J k)) step q ζ
        (idealResidualCoefficient P Q h ξ none) Ψ x f g +
      ∑ A ∈ probes₁.powerset.erase ∅, ∑ B ∈ probes₂.powerset.erase ∅,
        giantTwoSidedPhysicalPatternCutoffPairing (idealResidualCopied (some (A,B))) step q ζ
          (idealResidualCoefficient P Q h ξ (some (A,B))) Ψ x f g := by
  rw [giantTwoSidedPhysicalCutoffPairing_sum_patterns]
  have hd : Disjoint ({none} : Finset (IdealResidualPattern J k))
      ((probes₁.powerset.erase ∅ ×ˢ probes₂.powerset.erase ∅).image some) := by
    apply disjoint_singleton_left.mpr
    simp
  unfold idealResidualPatterns
  rw [sum_union hd, sum_singleton, sum_image]
  · rw [sum_product]
  · intro a _ b _ hab
    exact Option.some.inj hab

theorem giantTwoSidedPhysicalRawCutoffPairing_norm_le
    (probes₁ probes₂ : Finset (J × Fin k)) (step : ℤ) (q ζ : ℝ)
    (Q : ℕ) (h ξ : ℝ) (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    ‖giantTwoSidedPhysicalPatternCutoffPairing
        (idealResidualCopied (none : IdealResidualPattern J k)) step q ζ
        (idealResidualCoefficient P Q h ξ none) Ψ x f g‖ ≤
      ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
        idealResidualCopied step q ζ (idealResidualCoefficient P Q h ξ) Ψ x f g‖ +
      ∑ A ∈ probes₁.powerset.erase ∅, ∑ B ∈ probes₂.powerset.erase ∅,
        ‖giantTwoSidedPhysicalPatternCutoffPairing (idealResidualCopied (some (A,B))) step q ζ
          (idealResidualCoefficient P Q h ξ (some (A,B))) Ψ x f g‖ := by
  let comparisons := ∑ A ∈ probes₁.powerset.erase ∅, ∑ B ∈ probes₂.powerset.erase ∅,
    giantTwoSidedPhysicalPatternCutoffPairing (idealResidualCopied (some (A,B))) step q ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) Ψ x f g
  have hexp := giantTwoSidedPhysicalCutoffPairing_residual_expansion
    probes₁ probes₂ step q ζ Q h ξ Ψ x f g
  have hsum : ‖comparisons‖ ≤
      ∑ A ∈ probes₁.powerset.erase ∅, ∑ B ∈ probes₂.powerset.erase ∅,
        ‖giantTwoSidedPhysicalPatternCutoffPairing (idealResidualCopied (some (A,B))) step q ζ
          (idealResidualCoefficient P Q h ξ (some (A,B))) Ψ x f g‖ := by
    apply (norm_sum_le _ _).trans
    exact sum_le_sum (fun A _ => norm_sum_le _ _)
  calc
    _ = ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
        idealResidualCopied step q ζ (idealResidualCoefficient P Q h ξ) Ψ x f g - comparisons‖ := by
      rw [hexp]
      simp only [comparisons, add_sub_cancel_right]
    _ ≤ ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
        idealResidualCopied step q ζ (idealResidualCoefficient P Q h ξ) Ψ x f g‖ + ‖comparisons‖ :=
      norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl hsum

end
end ArtinMatthews
