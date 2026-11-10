module

public import ArtinMatthews.GiantTwoSidedResidueState
public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.GiantTwoSidedPatternTargetBudget
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

/-! The copied/free pattern acts by a deterministic translation of every
prime coordinate. All auxiliary masses and endpoint factors are literal. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def GiantTwoSidedResiduePatternCondition {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell : ℕ} (C : J → Finset (Fin k)) (step : ℤ)
    (s t : GiantTwoSidedResidueState P (k+ell)) (a : GiantTwoSidedPatternAuxiliary P C) : Prop :=
  (∀ j (i : Fin k),i∉C j → t.val.2 j (Fin.castAdd ell i)=s.val.2 j (Fin.castAdd ell i)) ∧
    t.val.1=giantTwoSidedResidueTranslate
      (step*((giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a:ℕ):ℤ)) s.val.1 ∧
    ∀ g j (i : ↥(C g)) (l : Fin (k+ell)),
      (a g i:ℕ)≠(s.val.2 j l:ℕ) ∧ (a g i:ℕ)≠(t.val.2 j l:ℕ)

theorem giantTwoSidedResiduePatternCondition_reverse {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} (C : J → Finset (Fin k)) (step : ℤ)
    (s t : GiantTwoSidedResidueState P (k+ell)) (a : GiantTwoSidedPatternAuxiliary P C)
    (h : GiantTwoSidedResiduePatternCondition C step s t a) :
    GiantTwoSidedResiduePatternCondition C (-step) t s a := by
  refine ⟨fun j i hi => (h.1 j i hi).symm,?_,fun g j i l => (h.2.2 g j i l).symm⟩
  rw [giantTwoSidedPatternCopiedProduct_eq h.1,neg_mul,h.2.1,
    giantTwoSidedResidueTranslate_neg]

def giantTwoSidedResiduePatternCoefficient {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (s t : GiantTwoSidedResidueState P (k+ell)) (a : GiantTwoSidedPatternAuxiliary P C) : ℂ :=
  if GiantTwoSidedResiduePatternCondition C step s t a then
    (giantTwoSidedPatternAuxiliaryMass a:ℂ)*(giantTwoSidedPatternFreshMass P C ell:ℂ)*K s.val.2 t.val.2 a*
      ((giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a:ℕ):ℂ)^
        ((ζ:ℂ)*Complex.I)*
      (giantTwoSidedResidueDamping P (k+ell) q s.val.1:ℂ)*
      (giantTwoSidedResidueDamping P (k+ell) q t.val.1:ℂ)
  else 0

theorem giantTwoSidedResiduePatternCoefficient_norm {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) (hV : ∀ j,0<bandReciprocalMass (P j))
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) {q : ℝ} (hq : 0≤q) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (s t : GiantTwoSidedResidueState P (k+ell)) (a : GiantTwoSidedPatternAuxiliary P C) :
    ‖giantTwoSidedResiduePatternCoefficient step q ζ K s t a‖=
      if GiantTwoSidedResiduePatternCondition C step s t a then
        giantTwoSidedPatternAuxiliaryMass a*giantTwoSidedPatternFreshMass P C ell*‖K s.val.2 t.val.2 a‖*
          giantTwoSidedResidueDamping P (k+ell) q s.val.1*
          giantTwoSidedResidueDamping P (k+ell) q t.val.1
      else 0 := by
  unfold giantTwoSidedResiduePatternCoefficient
  split_ifs
  · have hD : 0<giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a :=
      Nat.mul_pos (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (s.val.2 j (Fin.castAdd ell i)).property).pos)
        (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (a j i).property).pos)
    have hζ : ‖((giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a:ℕ):ℂ)^
        ((ζ:ℂ)*Complex.I)‖=1 := by
      rw [Complex.norm_natCast_cpow_of_pos hD]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,
        mul_zero,zero_mul,sub_self,Real.rpow_zero]
    have hq' (r : GiantTwoSidedFullResidue P) : 0≤giantTwoSidedResidueDamping P (k+ell) q r :=
      Real.rpow_nonneg hq _
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (giantTwoSidedPatternAuxiliaryMass_nonneg hV a),
      abs_of_nonneg (giantTwoSidedPatternFreshMass_nonneg C ell hV),abs_of_nonneg (hq' _),hζ,mul_one]
  · exact norm_zero

def giantTwoSidedResiduePatternTargets {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ)
    (s : GiantTwoSidedResidueState P (k+ell)) (a : GiantTwoSidedPatternAuxiliary P C) :
    Finset (GiantTwoSidedResidueState P (k+ell)) :=
  univ.filter (fun t => GiantTwoSidedResiduePatternCondition C step s t a)

theorem giantTwoSidedResiduePatternTargets_position {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell : ℕ} {C : J → Finset (Fin k)} {step : ℤ}
    {s t t' : GiantTwoSidedResidueState P (k+ell)} {a : GiantTwoSidedPatternAuxiliary P C}
    (ht : t∈giantTwoSidedResiduePatternTargets step s a)
    (ht' : t'∈giantTwoSidedResiduePatternTargets step s a) : t.val.1=t'.val.1 :=
  (mem_filter.mp ht).2.2.1.trans (mem_filter.mp ht').2.2.1.symm

theorem giantTwoSidedResiduePatternTargets_budget {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell : ℕ} {C : J → Finset (Fin k)} {step : ℤ}
    {s t₀ : GiantTwoSidedResidueState P (k+ell)} {a : GiantTwoSidedPatternAuxiliary P C}
    (ht₀ : t₀∈giantTwoSidedResiduePatternTargets step s a)
    {q B : ℝ} (hq : 0<q) (hV : ∀ j,0<bandReciprocalMass (P j))
    (hbudget : ∀ (j : J) (z : ℕ),
      (bandReciprocalMass (P j))⁻¹^(ell+(C j).card)*
      ((z:ℝ)+((ell+(C j).card:ℕ):ℝ))^(ell+(C j).card)*q^((z:ℝ)/2)≤B) :
    ((giantTwoSidedResiduePatternTargets step s a).card:ℝ)*
      giantTwoSidedPatternFreshMass P C ell*giantTwoSidedResidueDamping P (k+ell) q t₀.val.1≤
        B^Fintype.card J := by
  let T := giantTwoSidedResiduePatternTargets step s a
  let n := giantTwoSidedResidueZeroProduct t₀.val.1
  let A (j : J) := GiantTwoSidedPatternCompletion (P j) (C j) n (s.val.2 j)
  let f (t : ↥T) (j : J) : A j := by
    have ht : GiantTwoSidedResiduePatternCondition C step s t.val a := (mem_filter.mp t.property).2
    have hn : t.val.val.1=t₀.val.1 := giantTwoSidedResiduePatternTargets_position t.property ht₀
    refine ⟨t.val.val.2 j,t.val.property.1 j,?_,ht.1 j⟩
    intro l
    apply (giantTwoSidedResidueZeroProduct_dvd_iff hP t₀.val.1
      (giantTwoSidedResidueIndex j (t.val.val.2 j l))).mpr
    rw [← hn]
    exact t.val.property.2 j l
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact giantTwoSidedResiduePatternTargets_position u.property v.property
    · funext j
      exact congrArg (fun b : A j => b.val) (congrFun huv j)
  have hcard : (T.card:ℝ)≤(Fintype.card (∀ j,A j):ℝ) := by
    have h := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe] at h
    exact_mod_cast h
  rw [giantTwoSidedResidueDamping_eq_physical hP]
  calc
    _ ≤ (Fintype.card (∀ j,A j):ℝ)*giantTwoSidedPatternFreshMass P C ell*
        giantTwoSidedEndpointDamping P (k+ell) q n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (giantTwoSidedPatternFreshMass_nonneg C ell hV))
        (Real.rpow_nonneg hq.le _)
    _ ≤ _ := giantTwoSidedPatternCompletionProduct_budget P hdis C s.val.2 s.property.1
      (f ⟨t₀,ht₀⟩) hq hV (fun j => hbudget j _)

end
end ArtinMatthews
