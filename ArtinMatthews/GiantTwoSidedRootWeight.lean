module

public import ArtinMatthews.GiantTwoSidedRootLabelEquiv
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
public import ArtinMatthews.GiantTwoSidedPatternPathDamping
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

/-! The full physical path coefficient separates into its original
root-independent factors and the actual root-residue product. The
initial mass and both endpoint half-dampings are preserved. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedRootResidueFactor {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ) (root : ℤ) : ℝ :=
  ∏ v : Fin (n+1),
    (∏ j,∏ p∈markedPhysicalLabelSet (labels v) j,
      if (p:ℤ)∣root+offset v then (1:ℝ) else 0) *
    (∏ j,∏ p∈P j \ markedPhysicalLabelSet (labels v) j,
      if (p:ℤ)∣root+offset v then markedMemoryVisitQ q n v else 1)

def giantTwoSidedRootScalar {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (ζ : Fin n → ℝ)
    (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell):ℂ)*
    ∏ i : Fin n,
      (giantTwoSidedPatternAuxiliaryMass (aux i):ℂ)*
      (giantTwoSidedPatternFreshMass P (C i) ell:ℂ)*
      K i (giantTwoSidedPermuteLabels (π i) (labels i.castSucc))
        (giantTwoSidedPermuteLabels (τ i) (labels i.succ)) (aux i)*
      (giantTwoSidedPatternDilation (C i)
        (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) (aux i):ℂ)^((ζ i:ℂ)*Complex.I)

def giantTwoSidedRootWeight {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    {I : Finset ℕ} (d : GiantTwoSidedRootLabelData (P:=P) k ell n I) : ℂ :=
  giantTwoSidedRootScalar C d.2 π τ aux ζ K *
    (giantTwoSidedRootResidueFactor P d.2 q
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.2 π aux step)) (d.1.val:ℤ):ℂ)

theorem giantTwoSidedPhysicalPath_root_weight {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell n : ℕ} (hn : n≠0) {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}
    {I Z : Finset ℕ} (s : GiantTwoSidedPhysicalPath C π τ aux step I Z)
    {q : ℝ} (hq : 0≤q) (ζ : Fin n → ℝ)
    (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) :
    (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell):ℂ)*
      (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedEndpointPermute (π i) (s.val i.castSucc))
        (giantTwoSidedEndpointPermute (τ i) (s.val i.succ)) (aux i)) =
      giantTwoSidedRootWeight C π τ aux step q ζ K (giantTwoSidedRootLabel_encode s).val := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ m =>
    have hd := congrArg (fun a : ℝ => (a:ℂ))
      (giantTwoSidedPatternPath_residue_factor hdis s.val π τ aux step s.property.edges hq)
    have hc (i : Fin (m+1)) :
        giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
          (giantTwoSidedEndpointPermute (π i) (s.val i.castSucc))
          (giantTwoSidedEndpointPermute (τ i) (s.val i.succ)) (aux i) =
        (giantTwoSidedPatternAuxiliaryMass (aux i):ℂ)*
          (giantTwoSidedPatternFreshMass P (C i) ell:ℂ)*
          K i (giantTwoSidedPermuteLabels (π i) (s.val i.castSucc).val.2)
            (giantTwoSidedPermuteLabels (τ i) (s.val i.succ).val.2) (aux i)*
          (giantTwoSidedPatternDilation (C i)
            (giantTwoSidedPermuteLabels (π i) (s.val i.castSucc).val.2) (aux i):ℂ)^((ζ i:ℂ)*Complex.I)*
          (giantTwoSidedEndpointDamping P (k+ell) q (s.val i.castSucc).val.1.val:ℂ)*
          (giantTwoSidedEndpointDamping P (k+ell) q (s.val i.succ).val.1.val:ℂ) := by
      rw [giantTwoSidedPatternPhysicalCoefficient,ite_eq_left (s.property.edges i)]
      rfl
    unfold giantTwoSidedRootWeight giantTwoSidedRootScalar
    simp only [show (giantTwoSidedRootLabel_encode s).val.2=(fun v => (s.val v).val.2) from rfl]
    change _ = _ * (giantTwoSidedPathResidueFactor P (fun v => (s.val v).val.2) q
      (giantTwoSidedPathOffset (giantTwoSidedPatternPathIncrement s.val π aux step))
        ((s.val 0).val.1.val:ℤ):ℂ)
    rw [← hd]
    simp only [hc,Complex.ofReal_prod,Complex.ofReal_mul,prod_mul_distrib]
    ring

end
end ArtinMatthews
