module

public import ArtinMatthews.GiantSignedActualBirthMemoCost
public import ArtinMatthews.GiantSignedActualBirthEventMass
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

/-! The complete actual capped event is bounded by its chronological
fresh-atom charges. No conditional row or trace inequality is assumed. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n H : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] [∀ g, ∀ p : PB g, NeZero p.val]
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedCappedBirthEventBoundary_norm_le
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (hdis : Pairwise (fun a b => Disjoint (PS a) (PS b)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {q ρ v vmin mass BS W Δ : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hmass : 1 ≤ mass) (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ)/2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hW : 0 ≤ W) (hΔ : 0 ≤ Δ)
    (hatom : ∀ g p, ν g p ≤ Δ) (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ mass)
    (budget : ℕ) (θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i a, a ∈ patterns i → ∀ g, (C i a g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (hrow : ∀ i, |visitQ i/ρ^2| + |-(1-visitQ i)/ρ| / v ≤ 1)
    (K : (i : Fin n) → (a : I) → GiantTwoSidedPatternCoefficient PB (C i a) ell)
    (hK : ∀ i a, a ∈ patterns i → ∀ x y aux, ‖K i a x y aux‖ ≤ W)
    (η : (i : Fin n) → (a : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i a) s.2.2 → ℂ)
    (hη : ∀ i a, a ∈ patterns i → ∀ s r, ‖η i a s r‖ ≤ 1)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) :
    ‖giantSignedCappedBirthEventBoundary H ν V q ρ θ n patterns C κ visitQ ζ K η σ‖ ≤
      (Δ^(giantSignedUniformBirthStageNonpivots σ .initial).card * mass^(Fintype.card B*(k+ell))) *
        ((∏ i, giantSignedActualBirthVisitCost V ρ visitQ v mass Δ σ i) *
          ∏ i, giantSignedActualBirthEdgeCost (S := S) ρ patterns v vmin mass budget BS W Δ σ i) := by
  let cost := (∏ i, giantSignedActualBirthVisitCost V ρ visitQ v mass Δ σ i) *
    ∏ i, giantSignedActualBirthEdgeCost (S := S) ρ patterns v vmin mass budget BS W Δ σ i
  have hC0 := giantSignedEdgeUniformConstant_nonneg (rateMax := vmin⁻¹) (massMax := mass)
    (tmax := ell+budget) hρ1 (zero_le_one.trans hv)
  have hc0 : 0 ≤ cost := by
    unfold cost giantSignedActualBirthVisitCost giantSignedActualBirthEdgeCost
    positivity
  have hRules := giantSignedActualBirthMemoRules_absolute hPB ν V q ρ θ patterns C κ visitQ ζ K η
    v vmin mass budget BS W Δ σ hPS hdis hVS hVB hν hvmin hV hmass hq hq1 hBS hbudget hρ hρ1 hv hW hΔ
    hatom hMass hC hK hη hrow
  have hcost := giantSignedActualBirthMemoRules_cost hPB ν V q ρ θ patterns C κ visitQ ζ K η
    v vmin mass budget BS W Δ σ (zero_le_one.trans hv) hρ1 hBS hW hΔ
  exact giantSignedCappedBirthEventBoundary_norm_le_of_rules hPS hPB hdis hVS ν hν V q ρ θ
    patterns C κ visitQ ζ K η v vmin mass budget BS W Δ σ hv hmass hΔ hatom hMass hRules cost hc0 hcost

end
end ArtinMatthews
