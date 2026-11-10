module

public import ArtinMatthews.GiantComparisonCutoffPairing
public import ArtinMatthews.GiantComparisonStripIdeal
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantComparisonStripActual
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

/-! The performed comparison uses all endpoint bands and places its
nonempty probe sets on the big bands. The actual source cores supply
the shared-label invariance for the entire normalized cutoff pairing. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateComparisonCutoff_eq_shared_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (γ : ℝ) (j : ℕ)
    (q : ℝ) (Ψ : ℝ → ℂ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) (k N : ℕ)
      (Z : Finset ℕ), Z ⊆ Ioc 0 N →
      ∀ (C : S → Finset (Fin k)),
      let P (g : S) := giantCandidateGroup x g.val
      ∀ K : GiantTwoSidedPatternCoefficient P C 1,
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      giantTwoSidedPhysicalPatternCutoffPairing (Z:=Z) C 1 q 0
          (giantComparisonCharacterCoefficient χ K) Ψ x
          (fun n => (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)*conj (F n))
          (fun t => (giantTwoSidedEndpointDamping P (k+1) q t.val.1.val : ℂ)*
            χ t.val.1.val*G t.val.1.val) =
        ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        ∑ a : GiantComparisonSharedEdge P C 1 N Z Z aux,
          giantComparisonSharedSummand x q Ψ χ F G K a := by
  filter_upwards [giantCandidateComparisonSharedInvariant_eventually e he hεq m hm γ j,
    giantCandidateSelectedGroups_geometry_eventually, giantCandidateFullPrimes_prime_upper_eventually,
    eventually_gt_atTop (0:ℝ)] with x hi hg hp hx
  intro S k N Z hZ C
  dsimp only
  intro K
  let P (g : S) := giantCandidateGroup x g.val
  have hP (g : S) (p : ℕ) (hp' : p ∈ P g) : p.Prime :=
    (hp p (mem_giantCandidateFullPrimes.mpr ⟨g.val,hp'⟩)).1
  exact giantComparisonCutoffPairing_eq_shared hP (hg S).1 hZ C hx q Ψ χ _ _ K
    (fun c w hw => (hi S k C c w hw).1) (fun c w hw => (hi S k C c w hw).2.1)
    (fun c => (hi S k C c 1 Nat.one_pos).2.2)

theorem giantCandidatePerformedComparisonCutoff_eq_shared_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (γ : ℝ) (j : ℕ)
    (q : ℝ) (Ψ : ℝ → ℂ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) (k N : ℕ)
      (Z : Finset ℕ), Z ⊆ Ioc 0 N →
      ∀ (A B : Finset (GiantCandidatePerformedBig S × Fin k)) (Q : ℕ) (h ξ : ℝ),
      let P (g : S) := giantCandidateGroup x g.val
      let C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
      let K : GiantTwoSidedPatternCoefficient P C 1 := giantCandidatePerformedCoefficient S
        (idealResidualCoefficient (giantCandidatePerformedBigBand S) Q h ξ (some (A,B)))
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      giantTwoSidedPhysicalPatternCutoffPairing (Z:=Z) C 1 q 0
          (giantComparisonCharacterCoefficient χ K) Ψ x
          (fun n => (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)*conj (F n))
          (fun t => (giantTwoSidedEndpointDamping P (k+1) q t.val.1.val : ℂ)*
            χ t.val.1.val*G t.val.1.val) =
        ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        ∑ a : GiantComparisonSharedEdge P C 1 N Z Z aux,
          giantComparisonSharedSummand x q Ψ χ F G K a := by
  filter_upwards [giantCandidateComparisonCutoff_eq_shared_eventually e he hεq hm χ γ j q Ψ] with x hx
  intro S k N Z hZ A B Q h ξ
  exact hx S k N Z hZ _ _

theorem giantCandidatePerformedComparisonCoefficient_join_free {x : ℝ}
    (S : Finset (GiantCandidateGroupIndex x)) {k ell : ℕ}
    (A B : Finset (GiantCandidatePerformedBig S × Fin k)) (Q : ℕ) (h ξ : ℝ) :
    let P (g : S) := giantCandidateGroup x g.val
    let C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
    let f (g : GiantCandidatePerformedBig S) := giantCandidatePerformedSplitEquiv S (.inr g)
    let K := giantCandidatePerformedCoefficient S
      (idealResidualCoefficient (giantCandidatePerformedBigBand S) (ell:=ell) Q h ξ (some (A,B)))
    ∀ (c : GiantComparisonSharedLabels P C) (b b' : GiantComparisonFreeLabels P C ell)
      (aux : GiantTwoSidedPatternAuxiliary P C),
      K (giantComparisonJoinLabels c b) (giantComparisonJoinLabels c b') aux =
        giantComparisonFreeCoefficient A B Q h ξ (fun g => b (f g)) (fun g => b' (f g))
          (fun g => aux (f g)) := by
  dsimp only
  intro c b b' aux
  exact idealResidualCoefficient_join_free A B Q h ξ
    (fun g => c (giantCandidatePerformedSplitEquiv S (.inr g))) _ _ _

end
end ArtinMatthews
