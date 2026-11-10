module

public import ArtinMatthews.GiantSignedCleanFiberKernel
public import ArtinMatthews.GiantSignedTotalStepClean
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

/-! The actual total-product clean operator on a fixed pending prime
list is a finite matrix, with the independent integer step retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedSmallPrefixProduct_pos {S : Type*} [Fintype S]
    {PS : S → Finset ℕ} {k : ℕ}
    (hP : ∀ j p, p ∈ PS j → p.Prime) (d : MarkedPhysicalMarking PS k) :
    0 < markedPhysicalMarkingProduct d :=
  Finset.prod_pos fun j _ => Finset.prod_pos fun i _ => (hP j _ (d j i).property).pos

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (j : B) (p : PB j), NeZero p.val]

abbrev GiantSignedSectorExtra (s : GiantSignedMemorySectors PB) (M : ℕ) :=
  MarkedPhysicalMarking PB M × GiantSignedResidues s.2

def giantSignedSectorCleanApply {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (d : MarkedPhysicalMarking PS k) (κ : ℤ) (s : GiantSignedMemorySectors PB)
    (f : GiantSignedResidueFiber PS s.2 → MarkedPhysicalMarking PB (k+ell) → ℂ)
    (x : GiantSignedResidueFiber PS s.2) (a : MarkedPhysicalMarking PB (k+ell)) : ℂ :=
  (markedPhysicalMarkingProduct d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
    giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C
      (θ * (markedPhysicalMarkingProduct d : ℝ)) ζ K
      (giantSignedResidueDiagonal PS s.2 (κ * (markedPhysicalMarkingProduct d : ℤ)))
      (giantSignedSectorPendingDamping PS ρ s) (giantSignedSectorPendingDamping PS ρ s) f x a

omit [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
  [∀ (j : B) (p : PB j), NeZero p.val] in
theorem giantSignedTotalStepCleanApply_sector {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (d : MarkedPhysicalMarking PS k) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (s : GiantSignedMemorySectors PB) (x : GiantSignedResidueFiber PS s.2)
    (a : MarkedPhysicalMarking PB (k+ell)) :
    giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K
        (markedPhysicalMarkingProduct d) κ f x.1 a (giantSignedMemoryAt s x.2) =
      giantSignedSectorCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
        (giantSignedAmbientToSectors PS f s) x a := by
  rw [giantSignedTotalStepCleanApply_eq]
  unfold giantSignedSectorCleanApply
  apply congrArg (fun z : ℂ => (markedPhysicalMarkingProduct d : ℂ) ^ ((ζ : ℂ) * Complex.I) * z)
  have h := giantSignedAmbientCleanApply_at PS freshLaw auxLaw patterns C
    (θ * (markedPhysicalMarkingProduct d : ℝ)) ζ ρ K
    (κ * (markedPhysicalMarkingProduct d : ℤ)) f
  exact congrFun (congrFun (congrFun h s) x) a

def giantSignedSectorCleanKernel {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (d : MarkedPhysicalMarking PS k) (κ : ℤ) (s : GiantSignedMemorySectors PB)
    (x : GiantSignedResidueFiber PS s.2) (a : MarkedPhysicalMarking PB (k+ell))
    (y : GiantSignedResidueFiber PS s.2) (b : MarkedPhysicalMarking PB (k+ell)) : ℂ :=
  (markedPhysicalMarkingProduct d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
    giantSignedDampedCleanFiberKernel freshLaw auxLaw patterns C
      (θ * (markedPhysicalMarkingProduct d : ℝ)) ζ K
      (giantSignedResidueDiagonal PS s.2 (κ * (markedPhysicalMarkingProduct d : ℤ)))
      (giantSignedSectorPendingDamping PS ρ s) (giantSignedSectorPendingDamping PS ρ s) x a y b

theorem giantSignedSectorCleanApply_eq_sum_kernel {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (d : MarkedPhysicalMarking PS k) (κ : ℤ) (s : GiantSignedMemorySectors PB)
    (f : GiantSignedResidueFiber PS s.2 → MarkedPhysicalMarking PB (k+ell) → ℂ)
    (x : GiantSignedResidueFiber PS s.2) (a : MarkedPhysicalMarking PB (k+ell)) :
    giantSignedSectorCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ s f x a =
      ∑ y : GiantSignedResidueFiber PS s.2, ∑ b : MarkedPhysicalMarking PB (k+ell),
        giantSignedSectorCleanKernel PS freshLaw auxLaw patterns C θ ζ ρ K d κ s x a y b * f y b := by
  unfold giantSignedSectorCleanApply
  rw [giantSignedDampedCleanFiberApply_eq_sum_kernel]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro b _
  unfold giantSignedSectorCleanKernel
  ring

end
end ArtinMatthews
