module

public import ArtinMatthews.MarkedPhysicalRootIncidenceError
public import ArtinMatthews.MarkedPhysicalRootHaarLines
public import ArtinMatthews.MarkedPhysicalBadArcFamily
public import ArtinMatthews.MarkedPhysicalRootArcSum
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact original-root sum and main/error identity with target-dependent
residue incidence retained in every summand. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalRootIncidenceMajorantSum
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (S : ℕ) [NeZero S] (A B C D : ℝ)
    (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop) : ℝ :=
  ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
    ∑ p ∈ fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true,
      ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
        if E g z then ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ *
          (if |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 then
            markedRawBadRootArcMajorant e x d₀ Y source
              (((p.2.1 : ℝ)/(p.1 : ℝ)) : AddCircle (1 : ℝ)) else 0)
        else 0

theorem markedPhysicalRootIncidenceMajorantSum_eq_counts
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (S : ℕ) [NeZero S] (A B C D : ℝ)
    (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop)
    (hA : 1 < A) (hfirst : Y^(-7/10 : ℝ)<1/2)
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j)))<1/2) :
    markedPhysicalRootIncidenceMajorantSum e x source d₀ Y S A B C D d b a R Q ψ E =
      ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        ∑ iz ∈ Finset.univ.product (markedPhysicalRootTargetWindow d R Y),
          if E g iz.2 then
            markedPhysicalBadArcCoefficient e x source d₀ Y iz.1 *
              ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
                ((markedPhysicalRootStripPoints g A B
                  (markedPhysicalBadArcLower e x source d₀ Y iz.1)
                  (markedPhysicalBadArcUpper e x source d₀ Y iz.1) C D iz.2).card : ℝ)
          else 0 := by
  unfold markedPhysicalRootIncidenceMajorantSum
  apply Finset.sum_congr rfl
  intro g _
  have hh := markedPhysicalBadRootArc_weighted_root_sum e x source d₀ Y g A B C D hA
    (markedPhysicalRootTargetWindow d R Y)
    (fun z => if E g z then ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ else 0) hfirst hbeta
  calc
    _ = ∑ p ∈ fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true,
        ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
          (if E g z then ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ else 0) *
            (if |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 then
              markedRawBadRootArcMajorant e x d₀ Y source
                (((p.2.1 : ℝ)/(p.1 : ℝ)) : AddCircle (1 : ℝ)) else 0) := by
      simp only [ite_mul,zero_mul]
    _ = _ := by
      rw [hh,Finset.product_eq_sprod,Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp

theorem markedPhysicalRootIncidenceMajorantSum_error_eq
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (S : ℕ) [NeZero S] (A B C D U V : ℝ)
    (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop)
    (hA : 1 < A) (hfirst : Y^(-7/10 : ℝ)<1/2)
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j)))<1/2) :
    (markedPhysicalRootIncidenceMajorantSum e x source d₀ Y S A B C D d b a R Q ψ E -
      markedPhysicalRootIncidenceMain Finset.univ S A B C D
        (markedPhysicalBadArcLower e x source d₀ Y)
        (markedPhysicalBadArcUpper e x source d₀ Y)
        (markedPhysicalBadArcCoefficient e x source d₀ Y) d b a R Y Q ψ E)/(U*V) =
      ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        markedPhysicalRootIncidenceDiscrepancy Finset.univ g U V A B C D
          (markedPhysicalBadArcLower e x source d₀ Y)
          (markedPhysicalBadArcUpper e x source d₀ Y)
          (markedPhysicalBadArcCoefficient e x source d₀ Y) d b a R Y Q (E g) ψ := by
  rw [markedPhysicalRootIncidenceMajorantSum_eq_counts e x source d₀ Y S A B C D d b a R Q ψ E hA hfirst hbeta]
  unfold markedPhysicalRootIncidenceMain markedPhysicalRootIncidenceDiscrepancy
  rw [← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro iz _
  split_ifs <;> ring

end ArtinMatthews
