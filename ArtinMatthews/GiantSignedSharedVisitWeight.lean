module

public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.GiantSignedSourceVisitEnergy
public import ArtinMatthews.GiantSignedCappedStateBound
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

/-! One source memory weight controls both the signed projected visit and
the doubled absolute visit. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedProjectedVisit_energy_of_source_weights
    (N : ℕ) (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (V : B → ℝ) {Vmax qi ρ v C₀ L : ℝ}
    (hVmax : 0 ≤ Vmax) (hV0 : ∀ g, 0 ≤ V g) (hV : ∀ g, V g ≤ Vmax)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hρ : 0 < ρ) (hv : 0 < v) (hqi0 : 0 ≤ qi) (hqi1 : qi ≤ 1)
    (hL : 0 < L) (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (hrow : |qi / ρ ^ 2| + |-(1-qi) / ρ| / v ≤ 1)
    (hcolDouble : ∀ g, |qi / ρ ^ 2| + 2 * |-(1-qi) * V g / ρ| / v ≤ 1)
    (f : GiantSignedState PS PB M → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedProjectedVisit N ν V qi ρ f) ≤
      ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ Vmax ρ v) *
        giantSignedStateEnergy PS ν f := by
  have hcol (g : B) : |qi / ρ ^ 2| + |-(1-qi) * V g / ρ| / v ≤ 1 := by
    have h := hcolDouble g
    rw [mul_div_assoc] at h
    have hn : 0 ≤ |-(1-qi) * V g / ρ| / v := by positivity
    linarith
  obtain ⟨U, hU, hb⟩ := giantSignedStateMemoryCutoff_bound N f
  let w := giantSignedStateMemoryCutoff N f
  have he := giantSignedStateGhostGroup_energy PS hVS ν hν V qi ρ v hv hrow hcol w
    (giantSignedStateMemoryCutoff_memory_symmetric N f hsym) U 1 hU zero_lt_one
    (fun s a m => by simpa only [one_pow, mul_one] using hb (s,a,m))
  have hfactor := giantSignedSourceVisitFactor_le PB ν hν hMass V hVmax hV0 hV
    hρ hv.le hqi0 hqi1 hL hgroups
  refine (giantSignedStateMemoryCutoff_energy_le ν N (giantSignedChronologicalVisit ν V qi ρ w)).trans ?_
  exact he.trans ((mul_le_mul_left hfactor _).trans
    (mul_le_mul_right (giantSignedStateMemoryCutoff_energy_le ν N f) _))

end
end ArtinMatthews
