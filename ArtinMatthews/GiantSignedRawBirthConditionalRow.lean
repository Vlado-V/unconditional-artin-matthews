module

public import ArtinMatthews.GiantSignedRawConditionalMass
public import ArtinMatthews.GiantSignedRawFreshBirthGate
public import ArtinMatthews.GiantSignedRawConditionalRow
public import ArtinMatthews.GiantSignedRawFreshBirthMass
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

/-! Every dependent performed birth in the actual raw edge contributes
its single-point tilted prime factor to the weighted row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawEdgeBirthConditionalMass_row_bound {n H : ℕ}
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ v BS W Δ : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g) (hMass : 1 ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ)/2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (hW : 0 ≤ W) (hΔ : 0 ≤ Δ) (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (s : GiantSignedState PS PB (k+ell))
    (hatom : ∀ g p, ν g p ≤ Δ) (hνmass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) (i : Fin n)
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes)
    (hold : ∀ a, giantSignedUniformBirthOperation (k+ell) n H a = .edge i → old a = none) :
    giantSignedRawEdgeConditionalMass ν V κ q ρ θ ζ K s
      (fun c => giantSignedRawFreshBirthGate hPB σ i C c.2.1 old)
      (fun m => v^(∑ g, m.1 g)) ≤
      (W * Δ^(giantSignedUniformBirthStageNonpivots σ (.edge i)).card) *
        (v^(∑ g, s.2.2.1 g) *
          (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S) :=
  giantSignedRawEdgeConditionalMass_row_bound hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hv hW (pow_nonneg hΔ _) budget hC
    κ θ ζ K hK s (fun c => giantSignedRawFreshBirthGate hPB σ i C c.2.1 old)
    (fun c => giantSignedRawFreshBirthGate_mass hPB ν hν hΔ hMass hatom hνmass σ i C c.2.1 old hold)

end
end ArtinMatthews
