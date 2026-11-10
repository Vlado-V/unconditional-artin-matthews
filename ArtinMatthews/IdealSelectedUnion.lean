module

public import ArtinMatthews.IdealResidualFamily
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

/-! Disjoint selected probe sets carry exactly their two independent
harmonic product laws, with arbitrary tests pulled back unchanged. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSelectedUnionIndexEquiv {I : Type*} [DecidableEq I]
    (A B : Finset I) (hAB : Disjoint A B) : (↥A ⊕ ↥B) ≃ ↥(A ∪ B) where
  toFun u := match u with
    | Sum.inl a => ⟨a.val,mem_union_left B a.property⟩
    | Sum.inr b => ⟨b.val,mem_union_right A b.property⟩
  invFun v := if h : v.val∈A then Sum.inl ⟨v.val,h⟩ else
    Sum.inr ⟨v.val,(mem_union.mp v.property).resolve_left h⟩
  left_inv u := by
    cases u with
    | inl a => simp [a.property]
    | inr b =>
      have hb : b.val∉A := fun h => disjoint_left.mp hAB h b.property
      simp [hb]
  right_inv v := by
    dsimp
    split_ifs <;> rfl

def idealSelectedUnionEquiv {G : Type*} [DecidableEq G] (P : G → Finset ℕ) {M : ℕ}
    (A B : Finset (G × Fin M)) (hAB : Disjoint A B) :
    IdealSelectedLabels (idealResidualBands P (A ∪ B)) ≃
      IdealSelectedLabels (idealResidualBands P A) × IdealSelectedLabels (idealResidualBands P B) where
  toFun a := (fun v => a ⟨v.val,mem_union_left B v.property⟩,
    fun v => a ⟨v.val,mem_union_right A v.property⟩)
  invFun a v := if h : v.val∈A then a.1 ⟨v.val,h⟩ else a.2 ⟨v.val,(mem_union.mp v.property).resolve_left h⟩
  left_inv a := by
    funext v
    dsimp
    split_ifs <;> rfl
  right_inv a := by
    apply Prod.ext
    · funext v
      simp [v.property]
    · funext v
      have hv : v.val∉A := fun h => disjoint_left.mp hAB h v.property
      simp [hv]

theorem idealSelectedUnion_prod {G R : Type*} [DecidableEq G] [CommMonoid R]
    (P : G → Finset ℕ) {M : ℕ} (A B : Finset (G × Fin M)) (hAB : Disjoint A B)
    (F : ∀ g,↥(P g) → R) (a : IdealSelectedLabels (idealResidualBands P (A ∪ B))) :
    (∏ v : ↥(A ∪ B),F v.val.1 (a v))=
      (∏ v : ↥A,F v.val.1 ((idealSelectedUnionEquiv P A B hAB a).1 v))*
      ∏ v : ↥B,F v.val.1 ((idealSelectedUnionEquiv P A B hAB a).2 v) := by
  change (∏ v : ↥(A ∪ B),F v.val.1 (a v))=
    (∏ v : ↥A,F v.val.1 (a ⟨v.val,mem_union_left B v.property⟩))*
      ∏ v : ↥B,F v.val.1 (a ⟨v.val,mem_union_right A v.property⟩)
  have he := Equiv.prod_comp (idealSelectedUnionIndexEquiv A B hAB)
    (fun v : ↥(A ∪ B) => F v.val.1 (a v))
  rw [Fintype.prod_sum_type] at he
  simpa only [idealSelectedUnionIndexEquiv,Equiv.coe_fn_mk] using he.symm

theorem idealSelectedUnion_mass {G : Type*} [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (A B : Finset (G × Fin M)) (hAB : Disjoint A B)
    (a : IdealSelectedLabels (idealResidualBands P (A ∪ B))) :
    idealSelectedMass (idealResidualBands P (A ∪ B)) a=
      idealSelectedMass (idealResidualBands P A) (idealSelectedUnionEquiv P A B hAB a).1*
      idealSelectedMass (idealResidualBands P B) (idealSelectedUnionEquiv P A B hAB a).2 :=
  idealSelectedUnion_prod P A B hAB (fun g => markedHarmonicAtom (P g)) a

theorem idealSelectedUnion_product {G : Type*} [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (A B : Finset (G × Fin M)) (hAB : Disjoint A B)
    (a : IdealSelectedLabels (idealResidualBands P (A ∪ B))) :
    idealSelectedProduct a=idealSelectedProduct (idealSelectedUnionEquiv P A B hAB a).1*
      idealSelectedProduct (idealSelectedUnionEquiv P A B hAB a).2 :=
  idealSelectedUnion_prod P A B hAB (fun _ p => p.val) a

theorem idealSelectedUnion_expectation {G : Type*} [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (A B : Finset (G × Fin M)) (hAB : Disjoint A B)
    (F : IdealSelectedLabels (idealResidualBands P (A ∪ B)) → ℂ) :
    (∑ a,(idealSelectedMass (idealResidualBands P (A ∪ B)) a:ℂ)*F a)=
      ∑ a : IdealSelectedLabels (idealResidualBands P A),
        ∑ b : IdealSelectedLabels (idealResidualBands P B),
          (idealSelectedMass (idealResidualBands P A) a:ℂ)*
          (idealSelectedMass (idealResidualBands P B) b:ℂ)*F ((idealSelectedUnionEquiv P A B hAB).symm (a,b)) := by
  rw [← (idealSelectedUnionEquiv P A B hAB).symm.sum_comp,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [idealSelectedUnion_mass P A B hAB,Equiv.apply_symm_apply,Complex.ofReal_mul]

end
end ArtinMatthews
