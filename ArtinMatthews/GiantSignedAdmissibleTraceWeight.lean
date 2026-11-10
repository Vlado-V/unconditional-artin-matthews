module

public import ArtinMatthews.GiantSignedAdmissibleTraceEquiv
public import ArtinMatthews.GiantSignedTraceChronologyReplay
public import ArtinMatthews.GiantSignedTraceOfChronologyWeight
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

/-! The weighted admissible trace retains the complete original
coefficient after packing its exact chronological choices. -/

namespace ArtinMatthews
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}

private theorem heq_evaluate {X Y : Type*} {T : X → Type*} (f : (x : X) → T x → Y)
    {a b : X} {x : T a} {y : T b} (he : a = b) (ht : HEq x y) : f a x = f b y := by
  subst b
  exact congrArg (f a) (eq_of_heq ht)

variable (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)

local notation "One" => fun _ _ _ _ => (1 : ℂ)
local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One
local notation "Traces" => GiantSignedAdmissibleBirthTrace (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K

theorem giantSignedAdmissibleBirthTrace_weight_eq_chronology (x : Traces) :
    let z := giantSignedAdmissibleBirthTrace_pack ν V q ρ θ patterns C κ visitQ ζ K x
    ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν x.2.1 : ℝ) : ℂ) *
      giantSignedTraceWeight giantSignedBoundary Rows (x.1,x.2.1,giantSignedEmptyMemory PB) x.2.2.val =
      giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ
        (fun i => K i (z.val.1 i).val) z.val.2.2 := by
  let s : GiantSignedState PS PB (k+ell) := (x.1,x.2.1,giantSignedEmptyMemory PB)
  let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s x.2.2.val
  let mass := ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν x.2.1 : ℝ) : ℂ)
  have hAdm : GiantSignedChronologicalAdmissible κ z.history := x.2.2.property.1
  have hDist : GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.history) := x.2.2.property.2
  let replay := giantSignedTraceOfChronology ν V q ρ θ n patterns C κ visitQ ζ K
    z.pattern z.batch z.history hAdm.compatible
  have hr : HEq replay x.2.2.val :=
    giantSignedTraceChronology_replay ν V q ρ θ n patterns C κ visitQ ζ K s x.2.2.val hAdm.compatible
  have hw := heq_evaluate (giantSignedTraceWeight giantSignedBoundary Rows) z.first hr
  have hprod := giantSignedTraceOfChronology_weight ν V q ρ θ n patterns C κ visitQ ζ K
    z.pattern z.batch z.history hAdm.compatible hAdm.boundary.2
  have hmass : (giantSignedStateMass PS ν (z.history.state 0) : ℂ) = mass := by
    rw [z.first]
    simp only [s,mass,giantSignedStateMass,giantSignedEmptyMemory_mass,mul_one]
  change mass * giantSignedTraceWeight giantSignedBoundary Rows s x.2.2.val =
    giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ (fun i => K i (z.pattern i).val) z.history
  rw [giantSignedChronologicalDistinctWeight,ite_eq_left hDist,giantSignedChronologicalWeight,
    ite_eq_left ⟨hAdm.compatible,hAdm.boundary⟩,hmass,← hw,hprod]
  exact (mul_assoc _ _ _).symm

end
end ArtinMatthews
