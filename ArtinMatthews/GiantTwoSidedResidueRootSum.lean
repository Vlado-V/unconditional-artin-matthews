module

public import ArtinMatthews.GiantTwoSidedResiduePathFactor
public import ArtinMatthews.GiantTwoSidedRootWeight
public import ArtinMatthews.GiantTwoSidedResiduePathWeight
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

/-! Fixed pattern, permutation and auxiliary choices admit an exact
Haar root-tuple expansion with the original absolute root scalar. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def GiantTwoSidedResidueLabelGuard {J : Type*} {P : J → Finset ℕ} {k ell n : ℕ}
    (C : Fin n → J → Finset (Fin k)) (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell)) : Prop :=
  (∀ v,MarkedPhysicalMarkingDistinct (labels v)) ∧
    ∀ i,GiantTwoSidedLabelCompatible (C i)
      (giantTwoSidedPermuteLabels (π i) (labels i.castSucc))
      (giantTwoSidedPermuteLabels (τ i) (labels i.succ)) (aux i)

def giantTwoSidedIndependentResidueMean {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ) : ℝ :=
  (∑ root : GiantTwoSidedFullResidue P,giantTwoSidedIndependentResidueFactor P labels q offset root)/
    Fintype.card (GiantTwoSidedFullResidue P)

def giantTwoSidedResidueFixedPathMass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) : ℝ :=
  ∑ s : Fin (n+1) → GiantTwoSidedResidueState P (k+ell),
    giantTwoSidedResidueHaarStateMass P (k+ell)*
      ∏ i : Fin n,‖giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (s i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (s i.succ)) (aux i)‖

theorem giantTwoSidedResidueFixedPathMass_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) :
    giantTwoSidedResidueFixedPathMass C π τ aux step q ζ K=
      ∑ s : GiantTwoSidedResiduePath C π τ aux step,
        giantTwoSidedResidueHaarStateMass P (k+ell)*
          ∏ i : Fin n,‖giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
            (giantTwoSidedResiduePermute (π i) (s.val i.castSucc))
            (giantTwoSidedResiduePermute (τ i) (s.val i.succ)) (aux i)‖ := by
  let valid (s : Fin (n+1) → GiantTwoSidedResidueState P (k+ell)) :=
    ∀ i,GiantTwoSidedResiduePatternCondition (C i) (step i)
      (giantTwoSidedResiduePermute (π i) (s i.castSucc))
      (giantTwoSidedResiduePermute (τ i) (s i.succ)) (aux i)
  let W (s : Fin (n+1) → GiantTwoSidedResidueState P (k+ell)) :=
    giantTwoSidedResidueHaarStateMass P (k+ell)*
      ∏ i : Fin n,‖giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
        (giantTwoSidedResiduePermute (π i) (s i.castSucc))
        (giantTwoSidedResiduePermute (τ i) (s i.succ)) (aux i)‖
  have hs := Finset.sum_subtype (p:=valid) (F:=inferInstance) (univ.filter valid) (by simp) W
  change (∑ s,W s)=∑ s : {s // valid s},W s.val
  rw [← hs,sum_filter]
  apply sum_congr rfl
  intro s _
  by_cases h : valid s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    dsimp only [W]
    apply mul_eq_zero_of_right
    dsimp only [valid] at h
    push Not at h
    obtain ⟨i,hi⟩ := h
    apply prod_eq_zero (mem_univ i)
    rw [giantTwoSidedResiduePatternCoefficient,ite_eq_right hi,norm_zero]

def giantTwoSidedIndependentFixedPathMass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) : ℝ :=
  ∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
    if GiantTwoSidedResidueLabelGuard C π τ aux labels then
      ‖giantTwoSidedRootScalar C labels π τ aux ζ K‖*
        giantTwoSidedIndependentResidueMean labels q
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step))
    else 0

theorem giantTwoSidedResidueFixedPathMass_eq_rootMean {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hV : ∀ j,0<bandReciprocalMass (P j))
    {k ell n : ℕ} (C : Fin (n+1) → J → Finset (Fin k))
    (π τ : Fin (n+1) → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin (n+1) → ℤ)
    {q : ℝ} (hq : 0 ≤ q) (ζ : Fin (n+1) → ℝ)
    (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell) :
    giantTwoSidedResidueFixedPathMass C π τ aux step q ζ K=
      giantTwoSidedIndependentFixedPathMass C π τ aux step q ζ K := by
  let f (d : GiantTwoSidedResidueRootData P k ell (n+1)) :=
    (‖giantTwoSidedRootScalar C d.2 π τ aux ζ K‖/Fintype.card (GiantTwoSidedFullResidue P))*
      giantTwoSidedIndependentResidueFactor P d.2 q
        (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.2 π aux step)) d.1
  have hroot : giantTwoSidedResidueFixedPathMass C π τ aux step q ζ K=
      ∑ d : GiantTwoSidedResidueRootPath C π τ aux step,f d.val := by
    rw [giantTwoSidedResidueFixedPathMass_support]
    have he := (giantTwoSidedResidueRootEquiv C π τ aux step).symm.sum_comp
      (fun s : GiantTwoSidedResiduePath C π τ aux step =>
        giantTwoSidedResidueHaarStateMass P (k+ell)*
          ∏ i : Fin (n+1),‖giantTwoSidedResiduePatternCoefficient (step i) q (ζ i) (K i)
            (giantTwoSidedResiduePermute (π i) (s.val i.castSucc))
            (giantTwoSidedResiduePermute (τ i) (s.val i.succ)) (aux i)‖)
    rw [← he]
    apply sum_congr rfl
    intro d _
    exact giantTwoSidedResidueRoot_absolute_coefficient hP hdis hV d hq ζ K
  rw [hroot]
  let valid := GiantTwoSidedResidueRootCondition C π τ aux step
  have hs := Finset.sum_subtype (p:=valid) (F:=inferInstance) (univ.filter valid) (by simp) f
  rw [← hs,sum_filter]
  have hpoint (d : GiantTwoSidedResidueRootData P k ell (n+1)) :
      (if valid d then f d else 0)=
        if GiantTwoSidedResidueLabelGuard C π τ aux d.2 then f d else 0 := by
    have hc : valid d ↔ GiantTwoSidedResidueLabelGuard C π τ aux d.2 ∧
        ∀ v j l,giantTwoSidedResidueRootPosition C π aux step d v
          (giantTwoSidedResidueIndex j (d.2 v j l))=0 :=
      ⟨fun h => ⟨⟨h.distinct,h.compatible⟩,h.active⟩,
        fun h => ⟨h.1.1,h.1.2,h.2⟩⟩
    by_cases hg : GiantTwoSidedResidueLabelGuard C π τ aux d.2
    · by_cases ha : ∀ v j l,giantTwoSidedResidueRootPosition C π aux step d v
          (giantTwoSidedResidueIndex j (d.2 v j l))=0
      · rw [ite_eq_left (hc.mpr ⟨hg,ha⟩),ite_eq_left hg]
      · rw [ite_eq_right (fun h => ha (hc.mp h).2),ite_eq_left hg]
        have hf : f d=0 := by
          dsimp only [f]
          rw [giantTwoSidedIndependentResidueFactor_zero P d.2 q _ d.1 ha,mul_zero]
        exact hf.symm
    · rw [ite_eq_right (fun h => hg (hc.mp h).1),ite_eq_right hg]
  change (∑ d : GiantTwoSidedResidueRootData P k ell (n+1),if valid d then f d else 0)=_
  simp_rw [hpoint]
  rw [Fintype.sum_prod_type,sum_comm]
  unfold giantTwoSidedIndependentFixedPathMass
  apply sum_congr rfl
  intro labels _
  by_cases hg : GiantTwoSidedResidueLabelGuard C π τ aux labels
  · simp only [hg,ite_true]
    dsimp only [f,giantTwoSidedIndependentResidueMean]
    rw [← mul_sum]
    ring
  · simp [hg]

end
end ArtinMatthews
