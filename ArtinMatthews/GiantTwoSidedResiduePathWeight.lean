module

public import ArtinMatthews.GiantTwoSidedResiduePathFactor
public import ArtinMatthews.GiantTwoSidedRootWeight
public import ArtinMatthews.GiantTwoSidedResidueInitialMass
public import ArtinMatthews.MarkedPhysicalEndpointNorm
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

/-! The exact independent residue path coefficient separates into the
original root scalar and the full Haar-coordinate visit factor. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedResidueRoot_coefficient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell n : ℕ}
    {C : Fin (n+1) → J → Finset (Fin k)}
    {π τ : Fin (n+1) → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin (n+1) → ℤ}
    (d : GiantTwoSidedResidueRootPath C π τ aux step) {q : ℝ} (hq : 0 ≤ q)
    (ζ : Fin (n+1) → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) :
    (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell):ℂ)*
      (∏ i : Fin (n+1),giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (giantTwoSidedResidueRoot_reconstruct d i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (giantTwoSidedResidueRoot_reconstruct d i.succ)) (aux i))=
      giantTwoSidedRootScalar C d.val.2 π τ aux ζ K*
        (giantTwoSidedIndependentResidueFactor P d.val.2 q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.val.2 π aux step)) d.val.1:ℂ) := by
  have hd := congrArg (fun x : ℝ => (x:ℂ)) (giantTwoSidedResidueRoot_damping_factor hP hdis d hq)
  have hc (i : Fin (n+1)) :
      giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (giantTwoSidedResidueRoot_reconstruct d i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (giantTwoSidedResidueRoot_reconstruct d i.succ)) (aux i)=
      (giantTwoSidedPatternAuxiliaryMass (aux i):ℂ)*
        (giantTwoSidedPatternFreshMass P (C i) ell:ℂ)*
        K i (giantTwoSidedPermuteLabels (π i) (d.val.2 i.castSucc))
          (giantTwoSidedPermuteLabels (τ i) (d.val.2 i.succ)) (aux i)*
        (giantTwoSidedPatternDilation (C i)
          (giantTwoSidedPermuteLabels (π i) (d.val.2 i.castSucc)) (aux i):ℂ)^((ζ i:ℂ)*Complex.I)*
        (giantTwoSidedResidueDamping P (k+ell) q (giantTwoSidedResidueRoot_reconstruct d i.castSucc).val.1:ℂ)*
        (giantTwoSidedResidueDamping P (k+ell) q (giantTwoSidedResidueRoot_reconstruct d i.succ).val.1:ℂ) := by
    rw [giantTwoSidedResiduePatternCoefficient,
      ite_eq_left (giantTwoSidedResidueRoot_reconstruct_condition d i)]
    rfl
  rw [← hd]
  unfold giantTwoSidedRootScalar
  simp only [hc,Complex.ofReal_prod,Complex.ofReal_mul,prod_mul_distrib]
  ring

theorem giantTwoSidedResidueRoot_absolute_coefficient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j,0 < bandReciprocalMass (P j)) {k ell n : ℕ}
    {C : Fin (n+1) → J → Finset (Fin k)}
    {π τ : Fin (n+1) → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin (n+1) → ℤ}
    (d : GiantTwoSidedResidueRootPath C π τ aux step) {q : ℝ} (hq : 0 ≤ q)
    (ζ : Fin (n+1) → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) :
    giantTwoSidedResidueHaarStateMass P (k+ell)*
      (∏ i : Fin (n+1),‖giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (giantTwoSidedResidueRoot_reconstruct d i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (giantTwoSidedResidueRoot_reconstruct d i.succ)) (aux i)‖)=
      (‖giantTwoSidedRootScalar C d.val.2 π τ aux ζ K‖/Fintype.card (GiantTwoSidedFullResidue P))*
        giantTwoSidedIndependentResidueFactor P d.val.2 q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.val.2 π aux step)) d.val.1 := by
  have hσ := markedPhysicalMass_nonneg (fun j => bandReciprocalMass (P j)) (k+ell) (fun j => (hV j).le)
  have hf := giantTwoSidedIndependentResidueFactor_nonneg P d.val.2 hq
    (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.val.2 π aux step)) d.val.1
  have hw := congrArg norm (giantTwoSidedResidueRoot_coefficient hP hdis d hq ζ K)
  simp only [norm_mul,norm_prod,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ,abs_of_nonneg hf] at hw
  rw [giantTwoSidedResidueHaarStateMass_eq,div_mul_eq_mul_div,hw]
  ring

end
end ArtinMatthews
