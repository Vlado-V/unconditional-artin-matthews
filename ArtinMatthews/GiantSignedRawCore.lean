module

public import ArtinMatthews.GiantSignedRawCoreData
public import ArtinMatthews.GiantSignedEdgeEnergy
public import ArtinMatthews.GiantSignedSmallFreeEdge
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

/-! Energy of the full canonical core under its original copied law. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawCoreApply_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U u BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (aux : GiantTwoSidedPatternAuxiliary PB C)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedRawCoreApply ν V κ q ρ aux f) ≤
      ENNReal.ofReal ((BS ^ Fintype.card S) ^ 2 *
        (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B) *
          giantSignedStateEnergy PS ν f := by
  rw [giantSignedStateEnergy_copiedFree PS hVS ν hν C,
    giantSignedStateEnergy_copiedFree PS hVS ν hν C]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have he := giantSignedSmallFreeEdgeApply_energy hPS hdis hVS ν hν V
    hvmin hVmin hVmax hMass hq hq1 hBS hbudget hρ hρ1 hv hU hu
    (ell+budget) (fun g => Nat.add_le_add_left (hC g) ell) κ
    (giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct aux)
    (fun s a m => f (s, giantSignedPatternSourceFill C c a, m))
    (fun s a m => hf (s, giantSignedPatternSourceFill C c a, m))
    (fun s a => hsym s (giantSignedPatternSourceFill C c a))
  have hfun : (fun s a m => giantSignedRawCoreApply ν V κ q ρ aux f
      (s, giantSignedPatternSourceFill C c a, m)) =
      giantSignedSmallFreeEdgeApply ν V κ q ρ
        (giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct aux)
        (fun z b out => f (z, giantSignedPatternSourceFill C c b, out)) := by
    funext s a m
    exact giantSignedRawCoreApply_sourceFill ν V κ q ρ aux f c s a m
  rw [hfun]
  exact (mul_le_mul_right he (ENNReal.ofReal (giantSignedPatternCopiedMass ν c))).trans_eq (by ac_rfl)

end
end ArtinMatthews
