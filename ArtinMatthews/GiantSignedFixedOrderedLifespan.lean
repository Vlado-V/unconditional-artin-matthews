module

public import ArtinMatthews.GiantSignedLifespanOriginalPath
public import ArtinMatthews.GiantSignedLifespanBirthOrderSchedule
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

/-! A fixed original path, one supported choice for each actual big
prime, and the exact ordered batch at every visit. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ}

abbrev GiantSignedFixedLifespanChoices
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ) (q : Fin (n+1) → ℝ) :=
  {c : ∀ (g : B) (p : PB g), GiantSignedResidueLifespanChoice (path.visits g p) //
    ∀ g p, giantSignedResidueLifespanWeight p.val path.offset q (path.visits g p) (c g p) ≠ 0}

abbrev GiantSignedFixedOrderedLifespan
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) (ell : ℕ)
    (C : Fin n → B → Finset (Fin k)) (κ : Fin n → ℤ) (q : Fin (n+1) → ℝ) :=
  Σ path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ,
    Σ c : GiantSignedFixedLifespanChoices path q, GiantSignedLifespanBirthOrderSchedule c.val

abbrev GiantSignedFixedPackedChronology
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) (ell : ℕ)
    (C : Fin n → B → Finset (Fin k)) :=
  Σ batch : Fin (n+1) → B → ℕ, GiantSignedChronologicalChoices PS PB ell C batch

variable [DecidableEq S] [DecidableEq B]

abbrev GiantSignedFixedAdmissibleChronology
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) (ell : ℕ)
    (C : Fin n → B → Finset (Fin k)) (κ : Fin n → ℤ) :=
  {z : GiantSignedFixedPackedChronology PS PB ell C //
    GiantSignedChronologicalAdmissible κ z.2 ∧
      GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.2)}

def giantSignedFixedOrderedLifespan_chronology
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    {q : Fin (n+1) → ℝ} (x : GiantSignedFixedOrderedLifespan PS PB ell C κ q) :
    GiantSignedFixedPackedChronology PS PB ell C :=
  let data := x.1.schedule hP hdis hκ hsize x.2.1.property x.2.2
  ⟨data.batch,x.1.chronology data⟩

end
end ArtinMatthews
