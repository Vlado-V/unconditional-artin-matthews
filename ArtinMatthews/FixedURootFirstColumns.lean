module

public import ArtinMatthews.FixedURootPrescribedMatrix
public import ArtinMatthews.FixedURootReciprocalBoxes
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

/-! The counted completion triples have distinct primitive first columns.
Thus their cardinality is literally the number of primitive roots `(u,v)`,
with no multiplicity from the determinant-one completion. -/
namespace ArtinMatthews

/-- Determinant one and a canonical top-right entry make the completion unique. -/
theorem fixedURoot_canonical_entry_unique {u v c d c' d' : ℤ}
    (hc : 0 ≤ c) (hcu : c < u) (hc' : 0 ≤ c') (hcu' : c' < u)
    (hd : u*d-v*c = 1) (hd' : u*d'-v*c' = 1) : c = c' := by
  have hcop : IsCoprime u v := by
    refine ⟨d,-c,?_⟩
    linear_combination hd
  have hdiv : u ∣ v*(c'-c) := by
    refine ⟨d'-d,?_⟩
    linear_combination hd-hd'
  have hmod : Int.ModEq u c c' := Int.modEq_of_dvd (hcop.dvd_of_dvd_mul_left hdiv)
  change c%u = c'%u at hmod
  simpa only [Int.emod_eq_of_lt hc hcu,Int.emod_eq_of_lt hc' hcu'] using hmod

/-- Forget the uniquely determined completion coordinate. -/
def fixedURootFirstColumn (p : Σ _u : ℤ, ℤ × ℤ) : ℤ × ℤ := (p.1,p.2.2)

/-- On the actual canonical root-box set, forgetting `c` is injective. -/
theorem fixedURootFirstColumn_injOn {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1) :
    Set.InjOn fixedURootFirstColumn
      (fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV) := by
  rintro ⟨u,c,v⟩ hx ⟨u',c',v'⟩ hy he
  have hu : u = u' := congrArg Prod.fst he
  have hv : v = v' := congrArg Prod.snd he
  subst u'
  subst v'
  obtain ⟨d,_,_,hc,hcu,_,_,hd,_⟩ := fixedURootReciprocal_box_canonical hA hC hα hβ hx
  obtain ⟨d',_,_,hc',hcu',_,_,hd',_⟩ := fixedURootReciprocal_box_canonical hA hC hα hβ hy
  have hcc := fixedURoot_canonical_entry_unique hc.le hcu hc'.le hcu' hd hd'
  cases hcc
  rfl

/-- The literal set of primitive first columns for a prescribed matrix. -/
noncomputable def fixedURootMatrixFirstColumns {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool) : Finset (ℤ × ℤ) :=
  (fixedURootMatrixBoxPoints g₀ A B α β C D lcU rcU lcC rcC lcV rcV).image
    fixedURootFirstColumn

/-- Each primitive first column is counted once. -/
theorem fixedURootMatrixFirstColumns_card {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1) :
    (fixedURootMatrixFirstColumns g₀ A B α β C D lcU rcU lcC rcC lcV rcV).card =
      (fixedURootMatrixBoxPoints g₀ A B α β C D lcU rcU lcC rcC lcV rcV).card := by
  apply Finset.card_image_of_injOn
  exact fixedURootFirstColumn_injOn hA hC hα hβ


/-- Every counted pair is a positive primitive first column. -/
theorem fixedURootMatrixFirstColumns_primitive {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1) {u v : ℤ}
    (hmem : (u,v) ∈ fixedURootMatrixFirstColumns g₀ A B α β C D lcU rcU lcC rcC lcV rcV) :
    1 < u ∧ 1 < v ∧ IsCoprime u v := by
  obtain ⟨⟨w,c,z⟩,hp,he⟩ := Finset.mem_image.mp hmem
  change (w,z) = (u,v) at he
  cases he
  obtain ⟨d,hw,hz,_,_,_,_,hd,_⟩ := fixedURootReciprocal_box_canonical hA hC hα hβ hp
  refine ⟨hw,hz,?_⟩
  refine ⟨d,-c,?_⟩
  linear_combination hd

/-- Its unique canonical completion reduces to the actual prescribed matrix. -/
theorem fixedURootMatrixFirstColumns_completion {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1) {u v : ℤ}
    (hmem : (u,v) ∈ fixedURootMatrixFirstColumns g₀ A B α β C D lcU rcU lcC rcC lcV rcV) :
    ∃ c d : ℤ, 0 < c ∧ c < u ∧ 0 < d ∧ d < v ∧ u*d-v*c = 1 ∧
      ((!![(u : ZMod S), (c : ZMod S); (v : ZMod S), (d : ZMod S)] :
        Matrix (Fin 2) (Fin 2) (ZMod S)) = (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))) := by
  obtain ⟨⟨w,c,z⟩,hp,he⟩ := Finset.mem_image.mp hmem
  change (w,z) = (u,v) at he
  cases he
  obtain ⟨d,_,_,hc,hcu,hd,hdv,hdet,hdr⟩ := fixedURootReciprocal_box_canonical hA hC hα hβ hp
  refine ⟨c,d,hc,hcu,hd,hdv,hdet,?_⟩
  have hs := Finset.mem_sigma.mp hp
  have hur := (Finset.mem_filter.mp hs.1).2
  have hpair := (Finset.mem_filter.mp hs.2).2
  exact (fixedURootMatrix_modEq_iff g₀ u c v d).mpr ⟨hur,hpair.1,hpair.2.1,hdr⟩

end ArtinMatthews
