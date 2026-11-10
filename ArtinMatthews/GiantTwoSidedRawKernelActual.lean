module

public import ArtinMatthews.GiantTwoSidedRawKernel
public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantTwoSidedSharedInvariant
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

/-! The literal candidate cores and fixed character discharge every
arithmetic premise of the shared-product reindexing. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateRawPhysical_sum_eq_shared_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (γ : ℝ) (j : ℕ)
    (q : ℝ) (Ψ : ℝ → ℂ) :
    ∀ᶠ x : ℝ in atTop,∀ (S : Finset (GiantCandidateGroupIndex x)) (k N : ℕ)
      (Z Z' : Finset ℕ), Z ⊆ Ioc 0 N →
      let P (i : S) := giantCandidateGroup x i.val
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      (∑ r : GiantTwoSidedRawPhysicalEdge P k Z Z',giantTwoSidedRawPhysicalTerm x q Ψ χ F G r) =
        ∑ a : GiantTwoSidedRawSharedEdge P k N Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a := by
  filter_upwards [giantCandidateRawSharedEndpointInvariant_eventually e he hεq m hm γ j,
    giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually,
    eventually_gt_atTop (0:ℝ)] with x hi hg hp hx
  intro S k N Z Z' hZ
  let P (i : S) := giantCandidateGroup x i.val
  have hP (i : S) (p : ℕ) (h : p∈P i) : p.Prime :=
    (hp p (mem_giantCandidateFullPrimes.mpr ⟨i.val,h⟩)).1
  exact giantTwoSidedRawPhysical_sum_eq_shared hP (hg S).1 hZ hx q Ψ χ _ _
    (fun c w hw => (hi S k c w hw).1) (fun c w hw => (hi S k c w hw).2.1)
    (fun c => (hi S k c 1 Nat.one_pos).2.2)

end
end ArtinMatthews
