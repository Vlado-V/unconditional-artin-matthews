module

public import ArtinMatthews.GiantSignedAuxiliaryBan
public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.GiantSignedIdealBanError
public import ArtinMatthews.GiantSignedIdealEnergySum
public import ArtinMatthews.GiantSignedTiltedIdealBound
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exclusion error and the fresh-law error are added to the
original harmonic contraction before changing the active measure. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedIdeal_banned_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost ε : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hε : ∀ v ∈ patterns, 0 ≤ ε v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (hBan : ∀ v ∈ patterns, ∀ a b : MarkedPhysicalMarking P (k+ell),
      (∑ aux : GiantTwoSidedPatternAuxiliary P (C v),
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
          (if GiantSignedAuxiliaryBan (C v) a b aux then 0 else 1 : ℝ)) ≤ ε v)
    (U : ℝ) (hU : 0 ≤ U)
    (hOriginal : ∀ f : MarkedPhysicalMarking P (k+ell) → ℂ, IdealSymmetric f →
      idealLabelEnergy P (k+ell) (idealOperator patterns C Θ ζ K f) ≤
        U ^ 2 * idealLabelEnergy P (k+ell) f)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) :
    idealLabelEnergy P (k+ell)
      (idealOperator patterns C Θ ζ
        (fun v a b aux => if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0) f) ≤
      (U + ∑ v ∈ patterns, cost v * ε v) ^ 2 * idealLabelEnergy P (k+ell) f := by
  classical
  let A := idealOperator patterns C Θ ζ K f
  let T := idealOperator patterns C Θ ζ
    (fun v a b aux => if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0) f
  let D := fun a => -(A a - T a)
  let E := ∑ v ∈ patterns, cost v * ε v
  have hE : 0 ≤ E := Finset.sum_nonneg fun v hv => mul_nonneg (hcost v hv) (hε v hv)
  have hD : idealLabelEnergy P (k+ell) D ≤ E ^ 2 * idealLabelEnergy P (k+ell) f := by
    simpa only [idealLabelEnergy, D, norm_neg] using
      giantSignedIdeal_ban_error_energy hV hP patterns C Θ ζ K cost ε hcost hε hK hBan f
  let g : Bool → MarkedPhysicalMarking P (k+ell) → ℂ := fun b => if b then A else D
  let c : Bool → ℝ := fun b => if b then U else E
  have hc (b : Bool) (_ : b ∈ (Finset.univ : Finset Bool)) : 0 ≤ c b := by
    cases b
    · exact hE
    · exact hU
  have hg (b : Bool) (_ : b ∈ (Finset.univ : Finset Bool)) :
      idealLabelEnergy P (k+ell) (g b) ≤ (c b) ^ 2 * idealLabelEnergy P (k+ell) f := by
    cases b
    · exact hD
    · exact hOriginal f hf
  have hsum := giantSignedIdealEnergy_sum hV Finset.univ c hc f g hg
  have hgSum : (fun a => ∑ b : Bool, g b a) = T := by
    funext a
    simp [g, D]
  rw [hgSum] at hsum
  simpa [c, add_comm] using hsum

theorem giantSignedTiltedBannedIdeal_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 1 ≤ r j p)
    (R : ℝ) (hR : 0 ≤ R) (hrR : ∀ j p, r j p ≤ R)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost ε : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hε : ∀ v ∈ patterns, 0 ≤ ε v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (hBan : ∀ v ∈ patterns, ∀ a b : MarkedPhysicalMarking P (k+ell),
      (∑ aux : GiantTwoSidedPatternAuxiliary P (C v),
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
          (if GiantSignedAuxiliaryBan (C v) a b aux then 0 else 1 : ℝ)) ≤ ε v)
    (η U : ℝ) (hη : 0 ≤ η) (hU : 0 ≤ U)
    (hFresh : ∀ v ∈ patterns, ∀ b : MarkedPhysicalMarking P (k+ell),
      idealFreshTargetMass r (C v) b ≤ 1 + η)
    (hOriginal : ∀ f : MarkedPhysicalMarking P (k+ell) → ℂ, IdealSymmetric f →
      idealLabelEnergy P (k+ell) (idealOperator patterns C Θ ζ K f) ≤
        U ^ 2 * idealLabelEnergy P (k+ell) f)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) :
    (∑ a, giantSignedActiveMass (fun j p => markedHarmonicAtom (P j) p * r j p) a *
      ‖idealOperatorWithLaws (fun j p => markedHarmonicAtom (P j) p * r j p)
        (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ
        (fun v a b aux => if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0) f a‖ ^ 2) ≤
      R ^ (Fintype.card J * (k+ell)) *
        (U + (∑ v ∈ patterns, cost v * ε v) + η * ∑ v ∈ patterns, cost v) ^ 2 *
        ∑ a, giantSignedActiveMass (fun j p => markedHarmonicAtom (P j) p * r j p) a * ‖f a‖ ^ 2 := by
  classical
  let L : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell :=
    fun v a b aux => if GiantSignedAuxiliaryBan (C v) a b aux then K v a b aux else 0
  have hL (v : I) (hv : v ∈ patterns) (a b : MarkedPhysicalMarking P (k+ell))
      (aux : GiantTwoSidedPatternAuxiliary P (C v)) : ‖L v a b aux‖ ≤ cost v := by
    dsimp only [L]
    split_ifs
    · exact hK v hv a b aux
    · simpa using hcost v hv
  have hU' : 0 ≤ U + ∑ v ∈ patterns, cost v * ε v :=
    add_nonneg hU (Finset.sum_nonneg fun v hv => mul_nonneg (hcost v hv) (hε v hv))
  exact giantSignedTiltedIdeal_energy hV hP r hr R hR hrR patterns C Θ ζ L
    cost hcost hL η (U + ∑ v ∈ patterns, cost v * ε v) hη hU' hFresh
    (fun f hf => giantSignedIdeal_banned_energy hV hP patterns C Θ ζ K cost ε
      hcost hε hK hBan U hU hOriginal f hf) f hf

end
end ArtinMatthews
