module

public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.GiantSignedRawEdgeEnergy
public import ArtinMatthews.GiantSignedRawOldPermutation
public import ArtinMatthews.GiantSignedCappedStateBound
public import ArtinMatthews.GiantSignedRawEdgeSymmetry
public import ArtinMatthews.GiantSignedRawFamilyEnergy
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

/-! The actual projected raw edge family has the original full-state
energy bound, with no growth assumption on its test. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

theorem giantSignedProjectedRawEdgeFamilyApply_symmetric_of_equivariant
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (N : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ (s : GiantSignedState PS PB (k+ell))
      (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
      (r : GiantSignedRawEdgeMove PS PB ell (C i) (giantSignedMemoryPermute s.2.2 σ)),
      η i (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
        η i s (giantSignedRawEdgeOldEquiv s.2.2 σ r))
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η f (s,a,m)) := by
  unfold giantSignedProjectedRawEdgeFamilyApply
  exact giantSignedStateMemoryCutoff_memory_symmetric N _
    (giantSignedRawEdgeFamilyApply_symmetric_of_equivariant ν V patterns C κ q ρ θ ζ K η hη
      (giantSignedStateMemoryCutoff N f) (giantSignedStateMemoryCutoff_memory_symmetric N f hf))

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedProjectedRawEdgeFamilyApply_energy
    (N : ℕ) (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v BS W : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (hW : 0 ≤ W) (budget : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ i ∈ patterns, ∀ g, (C i g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ W)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ s r, ‖η i s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η f) ≤
      ENNReal.ofReal (giantSignedRawEdgeEnergyConstant ((patterns.card : ℝ) * W) BS
        (Fintype.card S) (Fintype.card B) ρ v vmin vmax massMax (ell+budget)) *
          giantSignedStateEnergy PS ν f := by
  obtain ⟨U, hU, hb⟩ := giantSignedStateMemoryCutoff_bound N f
  let w := giantSignedStateMemoryCutoff N f
  have hw : ∀ s, ‖w s‖ ≤ U * (1 : ℝ) ^ (∑ g, s.2.2.1 g) :=
    fun s => by simpa only [one_pow, mul_one] using hb s
  have he := giantSignedRawEdgeFamilyApply_energy hPS hPB hdis hVS hVB ν hν V hvmin hVmin hVmax
    hMass hq hq1 hBS hbudget hρ hρ1 hv hU le_rfl hW budget patterns C hC κ θ ζ K hK η hη w hw
    (giantSignedStateMemoryCutoff_memory_symmetric N f hsym)
  refine (giantSignedStateMemoryCutoff_energy_le ν N
    (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η w)).trans (he.trans ?_)
  exact mul_le_mul_right (giantSignedStateMemoryCutoff_energy_le ν N f) _

end
end ArtinMatthews
