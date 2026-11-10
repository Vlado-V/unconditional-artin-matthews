module

public import ArtinMatthews.IdealRawPairing
public import ArtinMatthews.IdealFirstCoordinates
public import ArtinMatthews.IdealSlotPairing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Every nonempty comparison sign is retained. The complete sum of
coordinate averages cancels directly to the two full-probe terms. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealRawPairing_sum_left {G I : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ) (s : Finset I)
    (f : I → MarkedPhysicalMarking P (k+ell) → ℂ) (g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ (fun a => ∑ i∈s,f i a) g=∑ i∈s,idealRawPairing P Θ ζ (f i) g :=
  idealLabelPairing_sum_left P s f _

theorem idealRawPairing_sum_right {G I : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ) (s : Finset I)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (g : I → MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ f (fun a => ∑ i∈s,g i a)=∑ i∈s,idealRawPairing P Θ ζ f (g i) := by
  unfold idealRawPairing
  simp only [mul_sum]
  exact idealLabelPairing_sum_right P s f _

theorem idealRawPairing_scalar_left {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ) (c : ℂ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ (fun a => c*f a) g=star c*idealRawPairing P Θ ζ f g :=
  idealLabelPairing_scalar_left P c f _

theorem idealRawPairing_scalar_right {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ) (c : ℂ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ f (fun a => c*g a)=c*idealRawPairing P Θ ζ f g := by
  unfold idealRawPairing idealLabelPairing
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

theorem idealRawPairing_sub_left {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ)
    (f₁ f₂ g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ (fun a => f₁ a-f₂ a) g=
      idealRawPairing P Θ ζ f₁ g-idealRawPairing P Θ ζ f₂ g := by
  unfold idealRawPairing idealLabelPairing
  simp only [star_sub,mul_sub,sub_mul,sum_sub_distrib]

theorem idealRawPairing_sub_right {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ)
    (f g₁ g₂ : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ f (fun a => g₁ a-g₂ a)=
      idealRawPairing P Θ ζ f g₁-idealRawPairing P Θ ζ f g₂ := by
  unfold idealRawPairing idealLabelPairing
  simp only [mul_sub,sum_sub_distrib]

theorem idealProbe_nonempty_average_sum {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (S : Finset (G × Fin k))
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (fun a => ∑ A∈S.powerset.erase ∅,(-1:ℂ)^A.card*
      idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f a)=
    fun a => idealProbeProjection P (idealFirstCoordinates ell S)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f a-
      idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f a := by
  funext a
  have he := congrFun (idealProbeProjection_first_coordinates P S f) a
  have hs := sum_erase_add S.powerset
    (fun A : Finset (G × Fin k) => (-1:ℂ)^A.card*
      idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f a)
    (show ∅∈S.powerset from mem_powerset.mpr (empty_subset _))
  have hf : idealResidualFreeSlots (∅ : Finset (G × Fin k))=(fun _ : G => (∅ : Finset (Fin k))) := by
    funext j
    ext i
    simp only [mem_idealResidualFreeSlots,notMem_empty]
  rw [hf,card_empty,pow_zero,one_mul,← he] at hs
  exact eq_sub_iff_add_eq.mpr hs

theorem idealRawPairing_nonempty_factor {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (S T : Finset (G × Fin k)) (Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ A∈S.powerset.erase ∅,∑ B∈T.powerset.erase ∅,(-1:ℂ)^(A.card+B.card)*
      idealRawPairing P Θ ζ
        (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
        (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g))=
    idealRawPairing P Θ ζ
      (fun a => ∑ A∈S.powerset.erase ∅,(-1:ℂ)^A.card*
        idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f a)
      (fun a => ∑ B∈T.powerset.erase ∅,(-1:ℂ)^B.card*
        idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g a) := by
  symm
  rw [idealRawPairing_sum_left]
  apply sum_congr rfl
  intro A _
  rw [idealRawPairing_scalar_left,idealRawPairing_sum_right,mul_sum]
  apply sum_congr rfl
  intro B _
  rw [idealRawPairing_scalar_right]
  simp only [star_pow,star_neg,star_one,pow_add,mul_assoc]

theorem idealResidual_raw_cancellation {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (S T : Finset (G × Fin k)) (Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ
      (idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)
      (idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g)-
    (∑ A∈S.powerset.erase ∅,∑ B∈T.powerset.erase ∅,(-1:ℂ)^(A.card+B.card)*
      idealRawPairing P Θ ζ
        (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
        (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g))=
    idealRawPairing P Θ ζ
      (idealProbeProjection P (idealFirstCoordinates ell S)
        (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)
      (idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g)+
    idealRawPairing P Θ ζ
      (fun a => idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f a-
        idealProbeProjection P (idealFirstCoordinates ell S)
          (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f a)
      (idealProbeProjection P (idealFirstCoordinates ell T)
        (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g) := by
  rw [idealRawPairing_nonempty_factor,idealProbe_nonempty_average_sum,idealProbe_nonempty_average_sum]
  simp only [idealRawPairing_sub_left,idealRawPairing_sub_right]
  ring

end
end ArtinMatthews
