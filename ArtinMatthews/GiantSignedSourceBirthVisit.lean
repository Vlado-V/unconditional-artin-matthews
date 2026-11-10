module

public import ArtinMatthews.GiantSignedSourceVisitEnergy
public import ArtinMatthews.GiantSignedGhostBirthApply
public import ArtinMatthews.GiantSignedGhostBirthEnergy
public import ArtinMatthews.GiantSignedGhostBirthSymmetry
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

/-! The literal bounded birth phases keep the same source visit weight
and energy exponent used in the unmodified projected word. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
universe u

variable {S B : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    [Fintype (GiantTwoSidedResidueState PS M)]

theorem giantSignedProjectedBirthVisit_energy_of_source_weights
    (H : ℕ) (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (V : B → ℝ) {vmax qi ρ v C₀ L : ℝ}
    (hvmax : 0 ≤ vmax) (hV0 : ∀ g, 0 ≤ V g) (hV : ∀ g, V g ≤ vmax)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hρ : 0 < ρ) (hv : 0 < v) (hqi0 : 0 ≤ qi) (hqi1 : qi ≤ 1)
    (hL : 0 < L) (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (hrow : |qi / ρ ^ 2| + |-(1-qi) / ρ| / v ≤ 1)
    (hcolDouble : ∀ g, |qi / ρ ^ 2| + 2 * |-(1-qi) * V g / ρ| / v ≤ 1)
    (φ : GiantSignedGhostBirthMultiplier PB) (hφ : ∀ b p, ‖φ b p‖ ≤ 1)
    (f : GiantSignedState PS PB M → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    let z := giantSignedProjectedBirthVisit H ν V qi ρ φ f
    (∀ s a, GiantSignedMemorySymmetric (fun m => z (s,a,m))) ∧
    giantSignedStateEnergy PS ν z ≤
      ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ vmax ρ v) *
        giantSignedStateEnergy PS ν f := by
  have hcol (g : B) : |qi / ρ ^ 2| + |-(1-qi) * V g / ρ| / v ≤ 1 := by
    have h := hcolDouble g
    rw [mul_div_assoc] at h
    have hn : 0 ≤ |-(1-qi) * V g / ρ| / v := by positivity
    linarith
  refine ⟨giantSignedProjectedBirthVisit_memorySymmetric H ν V qi ρ φ f hf, ?_⟩
  have he := giantSignedProjectedBirthVisit_energy (PS := PS) H hVS ν hν V
    qi ρ v hv hrow hcol φ hφ f hf
  have hfactor := giantSignedSourceVisitFactor_le PB ν hν hMass V hvmax hV0 hV
    hρ hv.le hqi0 hqi1 hL hgroups
  exact he.trans (mul_le_mul_left hfactor _)

end
end ArtinMatthews
