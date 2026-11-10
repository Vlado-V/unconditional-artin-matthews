module

public import ArtinMatthews.GiantSignedChronologicalSupport
public import ArtinMatthews.GiantSignedCappedBoundaryRank
public import ArtinMatthews.GiantSignedTraceChronologySupport
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The original weighted trace is supported on admissible chronological
choices with distinct births. The initial measure remains inside the weight. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)

local notation "One" => fun _ _ _ _ => (1 : ℂ)
local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One

abbrev GiantSignedAdmissibleBirthTraceAt (s : GiantSignedState PS PB (k+ell)) :=
  {t : GiantSignedTrace Rows s //
    let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s t
    GiantSignedChronologicalAdmissible κ z.history ∧
      GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.history)}

abbrev GiantSignedAdmissibleBirthTrace :=
  Σ y : GiantTwoSidedResidueState PS (k+ell), Σ a : MarkedPhysicalMarking PB (k+ell),
    GiantSignedAdmissibleBirthTraceAt ν V q ρ θ patterns C κ visitQ ζ K (y,a,giantSignedEmptyMemory PB)

theorem giantSignedTraceWeightedDistinct_eq_admissible_indicator
    (y : GiantTwoSidedResidueState PS (k+ell)) (a : MarkedPhysicalMarking PB (k+ell)) :
    let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
    let mass := ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ)
    ∀ t : GiantSignedTrace Rows s,
      let w := giantSignedTraceWeight giantSignedBoundary Rows s t
      let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s t
      mass * (w * giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K One s t) =
        if GiantSignedChronologicalAdmissible κ z.history ∧
          GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.history) then mass*w else 0 := by
  intro s mass t w z
  let distinct := GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.history)
  change mass * (w * (if distinct then (1:ℂ) else 0)) =
    if GiantSignedChronologicalAdmissible κ z.history ∧ distinct then mass*w else 0
  by_cases hd : distinct
  · rw [ite_eq_left hd, mul_one]
    by_cases hw : mass*w = 0
    · simp only [hw, ite_self]
    · have hw0 : w ≠ 0 := (mul_ne_zero_iff.mp hw).2
      obtain ⟨hc,hterm,hwprod⟩ := giantSignedTraceChronology_support ν V q ρ θ n patterns C κ visitQ ζ K s t hw0
      have hstart : (z.history.state 0).2.2 = giantSignedEmptyMemory PB :=
        congrArg (fun st : GiantSignedState PS PB (k+ell) => st.2.2) z.first
      have hstate : (giantSignedStateMass PS ν (z.history.state 0) : ℂ) = mass := by
        rw [z.first]
        simp only [s, mass, giantSignedStateMass, giantSignedEmptyMemory_mass, mul_one]
      have hweight : giantSignedChronologicalWeight ν V κ q visitQ ρ θ ζ (fun i => K i (z.pattern i).val) z.history =
          mass*w := by
        unfold giantSignedChronologicalWeight
        rw [ite_eq_left ⟨hc,hstart,hterm⟩, hstate]
        change w = _ at hwprod
        rw [hwprod]
        ring
      have ha := giantSignedChronologicalWeight_admissible ν V κ q visitQ ρ θ ζ
        (fun i => K i (z.pattern i).val) z.history (hweight.symm ▸ hw)
      rw [ite_eq_left ⟨ha,hd⟩]
  · simp only [hd, and_false, ite_false, mul_zero]

end
end ArtinMatthews
