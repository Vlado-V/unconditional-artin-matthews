module

public import ArtinMatthews.GiantTwoSidedEndpointStates
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The physical coefficient for a general copied/free pattern on
finite positive position slices. The copied product, auxiliary product,
auxiliary law, endpoint bans and both half-dampings are literal. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedPatternAuxiliary {J : Type*} (P : J → Finset ℕ) {k : ℕ}
    (C : J → Finset (Fin k)) := (j : J) → ↥(C j) → ↥(P j)

def giantTwoSidedPatternCopiedProduct {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) : ℕ :=
  ∏ j,∏ i ∈ univ \ C j,(a j (Fin.castAdd ell i):ℕ)

def giantTwoSidedPatternAuxiliaryProduct {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} {C : J → Finset (Fin k)}
    (a : GiantTwoSidedPatternAuxiliary P C) : ℕ :=
  ∏ j,∏ i : ↥(C j),(a j i:ℕ)

def giantTwoSidedPatternAuxiliaryMass {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} {C : J → Finset (Fin k)}
    (a : GiantTwoSidedPatternAuxiliary P C) : ℝ :=
  ∏ j,∏ i : ↥(C j),markedHarmonicAtom (P j) (a j i)

def giantTwoSidedPatternFreshMass {J : Type*} [Fintype J] (P : J → Finset ℕ)
    {k : ℕ} (C : J → Finset (Fin k)) (ell : ℕ) : ℝ :=
  ∏ j,(bandReciprocalMass (P j))⁻¹^(ell+(C j).card)

theorem giantTwoSidedPatternAuxiliaryMass_nonneg {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} {C : J → Finset (Fin k)}
    (hV : ∀ j,0 < bandReciprocalMass (P j)) (a : GiantTwoSidedPatternAuxiliary P C) :
    0 ≤ giantTwoSidedPatternAuxiliaryMass a :=
  prod_nonneg fun j _ => prod_nonneg fun _ _ => markedHarmonicAtom_nonneg (P j) (hV j)

theorem giantTwoSidedPatternAuxiliaryMass_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : ℕ} (C : J → Finset (Fin k))
    (hV : ∀ j,0 < bandReciprocalMass (P j)) :
    (∑ a : GiantTwoSidedPatternAuxiliary P C,giantTwoSidedPatternAuxiliaryMass a)=1 := by
  classical
  unfold giantTwoSidedPatternAuxiliaryMass
  rw [← Fintype.prod_sum (fun j (a : ↥(C j) → ↥(P j)) =>
    ∏ i : ↥(C j),markedHarmonicAtom (P j) (a i))]
  apply prod_eq_one
  intro j _
  rw [← Fintype.prod_sum (fun (_ : ↥(C j)) (p : ↥(P j)) => markedHarmonicAtom (P j) p)]
  simp only [markedHarmonicAtom_sum _ (hV j),prod_const_one]

theorem giantTwoSidedPatternFreshMass_nonneg {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} (C : J → Finset (Fin k)) (ell : ℕ)
    (hV : ∀ j,0 < bandReciprocalMass (P j)) :
    0 ≤ giantTwoSidedPatternFreshMass P C ell :=
  prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _

def GiantTwoSidedPatternCondition {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell : ℕ} (C : J → Finset (Fin k)) (step : ℤ) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (t : GiantTwoSidedEndpointState P (k+ell) Z')
    (a : GiantTwoSidedPatternAuxiliary P C) : Prop :=
  (∀ j (i : Fin k),i∉C j → t.val.2 j (Fin.castAdd ell i)=s.val.2 j (Fin.castAdd ell i)) ∧
    (t.val.1.val:ℤ) = (s.val.1.val:ℤ)+step*
      ((giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a:ℕ):ℤ) ∧
    ∀ g j (i : ↥(C g)) (l : Fin (k+ell)),
      (a g i:ℕ) ≠ (s.val.2 j l:ℕ) ∧ (a g i:ℕ) ≠ (t.val.2 j l:ℕ)

theorem giantTwoSidedPatternCopiedProduct_eq {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell : ℕ} {C : J → Finset (Fin k)} {s t : MarkedPhysicalMarking P (k+ell)}
    (h : ∀ j (i : Fin k),i∉C j → t j (Fin.castAdd ell i)=s j (Fin.castAdd ell i)) :
    giantTwoSidedPatternCopiedProduct C t=giantTwoSidedPatternCopiedProduct C s := by
  unfold giantTwoSidedPatternCopiedProduct
  exact prod_congr rfl fun j _ => prod_congr rfl fun i hi =>
    congrArg (fun p : ↥(P j) => p.val) (h j i (mem_sdiff.mp hi).2)

theorem giantTwoSidedPatternCondition_reverse {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} (C : J → Finset (Fin k)) (step : ℤ) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (t : GiantTwoSidedEndpointState P (k+ell) Z')
    (a : GiantTwoSidedPatternAuxiliary P C) (h : GiantTwoSidedPatternCondition C step s t a) :
    GiantTwoSidedPatternCondition C (-step) t s a := by
  refine ⟨fun j i hi => (h.1 j i hi).symm,?_,fun g j i l => (h.2.2 g j i l).symm⟩
  rw [giantTwoSidedPatternCopiedProduct_eq h.1,neg_mul]
  have hn := h.2.1
  omega

abbrev GiantTwoSidedPatternCoefficient {J : Type*} (P : J → Finset ℕ) {k : ℕ}
    (C : J → Finset (Fin k)) (ell : ℕ) :=
  MarkedPhysicalMarking P (k+ell) → MarkedPhysicalMarking P (k+ell) →
    GiantTwoSidedPatternAuxiliary P C → ℂ

def giantTwoSidedPatternPhysicalCoefficient {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (t : GiantTwoSidedEndpointState P (k+ell) Z')
    (a : GiantTwoSidedPatternAuxiliary P C) : ℂ :=
  if GiantTwoSidedPatternCondition C step s t a then
    (giantTwoSidedPatternAuxiliaryMass a:ℂ)*(giantTwoSidedPatternFreshMass P C ell:ℂ)*K s.val.2 t.val.2 a*
      ((giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a:ℕ):ℂ)^
        ((ζ:ℂ)*Complex.I) *
      (giantTwoSidedEndpointDamping P (k+ell) q s.val.1.val:ℂ)*
      (giantTwoSidedEndpointDamping P (k+ell) q t.val.1.val:ℂ)
  else 0

theorem giantTwoSidedPatternPhysicalCoefficient_norm {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (hV : ∀ j,0 < bandReciprocalMass (P j))
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) {q : ℝ} (hq : 0 ≤ q) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (t : GiantTwoSidedEndpointState P (k+ell) Z')
    (a : GiantTwoSidedPatternAuxiliary P C) :
    ‖giantTwoSidedPatternPhysicalCoefficient step q ζ K s t a‖ =
      if GiantTwoSidedPatternCondition C step s t a then
        giantTwoSidedPatternAuxiliaryMass a*giantTwoSidedPatternFreshMass P C ell*‖K s.val.2 t.val.2 a‖*
          giantTwoSidedEndpointDamping P (k+ell) q s.val.1.val*
          giantTwoSidedEndpointDamping P (k+ell) q t.val.1.val
      else 0 := by
  unfold giantTwoSidedPatternPhysicalCoefficient
  split_ifs
  · have hD : 0 < giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a :=
      Nat.mul_pos (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (s.val.2 j (Fin.castAdd ell i)).property).pos)
        (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (a j i).property).pos)
    have hζ : ‖((giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a:ℕ):ℂ)^
        ((ζ:ℂ)*Complex.I)‖=1 := by
      rw [Complex.norm_natCast_cpow_of_pos hD]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,
        mul_zero,zero_mul,sub_self,Real.rpow_zero]
    have hq' (n : ℕ) : 0 ≤ giantTwoSidedEndpointDamping P (k+ell) q n := Real.rpow_nonneg hq _
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (giantTwoSidedPatternAuxiliaryMass_nonneg hV a),
      abs_of_nonneg (giantTwoSidedPatternFreshMass_nonneg C ell hV),abs_of_nonneg (hq' _),hζ,mul_one]
  · exact norm_zero

end
end ArtinMatthews
