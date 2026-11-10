module

public import ArtinMatthews.MarkedPhysicalPadCofactorSum
public import ArtinMatthews.MarkedPhysicalScalarCofactor
public import ArtinMatthews.MarkedPhysicalPadCollisionMass
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

/-! Replace the two genuine cofactor fibers by the actual scalar support.
An absent pad or last-label distinctness flag still gives exactly zero. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysical_sum_supported_cofactor_pair {p q : ℕ × ℕ → Prop}
    [Fintype (Subtype p)] [Fintype (Subtype q)]
    (R : Finset (ℕ × ℕ)) (F : (ℕ × ℕ) → (ℕ × ℕ) → ℂ)
    (h : ∀ v u,F v u ≠ 0 → v ∈ R ∧ u ∈ R ∧
      (∃ v' : Subtype p,v'.1=v) ∧ (∃ u' : Subtype q,u'.1=u)) :
    (∑ v : Subtype p,∑ u : Subtype q,F v.1 u.1) = ∑ v ∈ R,∑ u ∈ R,F v u := by
  rw [← Fintype.sum_prod_type',← Finset.sum_product' R R F]
  apply Finset.sum_bij_ne_zero (fun i _ _ => (i.1.1,i.2.1))
  · intro i _ hi
    exact Finset.mem_product.mpr ⟨(h _ _ hi).1,(h _ _ hi).2.1⟩
  · intro i _ _ j _ _ hij
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hij)) (Subtype.ext (congrArg Prod.snd hij))
  · intro y _ hy
    obtain ⟨_,_,⟨v,hv⟩,⟨u,hu⟩⟩ := h _ _ hy
    exact ⟨(v,u),Finset.mem_univ _,by simpa only [hv,hu] using hy,Prod.ext hv hu⟩
  · intro i _ _
    rfl

variable {J : Type*} [Fintype J] [Nonempty J] (P : J → Finset ℕ)
  (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
  (pads : ℕ) (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j))
  {d₀ Y Hm Hn W : ℝ} (hd₀ : 0 ≤ d₀) (hY : 0 < Y) (hm₀ : 0 ≤ Hm) (hn₀ : 0 ≤ Hn)
  (hD : d₀ ≤ (markedPhysicalMarkingProduct c:ℝ) ∧ (markedPhysicalMarkingProduct c:ℝ) < 2*d₀)
  (hbelow : ∀ j p,p ∈ P j → (p:ℝ)<W)
  {η : ℝ → ℂ} (hη : Function.support η ⊆ Set.Icc 1 4)
  {detector : ℤ → ℤ → ℤ → ℂ} (ht : ∀ b a t : ℤ,detector b a t ≠ 0 → |(t:ℝ)| < W)
  {α β : ℕ → ℂ} (S T : Finset ℕ)
  (hS : ∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm)
  (hT : ∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn)
  (hα : ∀ m,α m ≠ 0 → m ∈ S ∧ MarkedPhysicalRoughAt W m)
  (hβ : ∀ n,β n ≠ 0 → n ∈ T ∧ MarkedPhysicalRoughAt W n)

include hd₀ hY hm₀ hn₀ hD hbelow hη ht hS hT hα hβ

theorem markedPhysicalPadCofactorBlock_eq_supported_sum :
    markedPhysicalPadCofactorBlock P hP hdis pads (markedPhysicalPadBox d₀ Y Hm Hn)
      (markedPhysicalPadBox_nonnegative hd₀ hY.le hm₀ hn₀) η Y detector α β c b a =
      if ¬MarkedPhysicalPadCollisionEvent P pads b a c ∧ (∀ j,b j ≠ a j) then
        ∑ v ∈ S.product T,∑ u ∈ S.product T,markedPhysicalScalarCofactorTerm η Y detector α β
          (markedPrimeBandProduct P b) (markedPrimeBandProduct P a) v u else 0 := by
  unfold markedPhysicalPadCofactorBlock
  let A := (markedPhysicalMarkingSplit pads).symm (c,a)
  let B := (markedPhysicalMarkingSplit pads).symm (c,b)
  let Z := markedPhysicalPadBox d₀ Y Hm Hn
  let hZ := markedPhysicalPadBox_nonnegative hd₀ hY.le hm₀ hn₀
  let _ := markedPhysicalCofactorCoordinates_fintype hP hdis hZ B
  let _ := markedPhysicalCofactorCoordinates_fintype hP hdis hZ A
  let F := markedPhysicalScalarCofactorTerm η Y detector α β
    (markedPrimeBandProduct P b) (markedPrimeBandProduct P a)
  by_cases h : ¬MarkedPhysicalPadCollisionEvent P pads b a c ∧ (∀ j,b j ≠ a j)
  · rw [ite_eq_left h]
    have hgood : ∀ j,¬MarkedPadCollision {b j,a j} (c j) :=
      fun j hj => h.1 ⟨j,hj⟩
    obtain ⟨_,hban⟩ := (markedPhysicalPad_source_crossBan_iff hdis c b a).mpr ⟨hgood,h.2⟩
    have hrough (m : ℕ) (hm : α m ≠ 0) : MarkedPhysicalBandRough P m :=
      markedPhysicalBandRough_of_rough P hP hbelow (hα m hm).2
    simp_rw [markedPhysicalPadCofactorTerm_eq_scalar η Y detector α β c b a hban hrough]
    change (∑ v : MarkedPhysicalCofactorCoordinates (Z := Z) B,
      ∑ u : MarkedPhysicalCofactorCoordinates (Z := Z) A,F v.1 u.1) = _
    refine @markedPhysical_sum_supported_cofactor_pair _ _
      (markedPhysicalCofactorCoordinates_fintype hP hdis hZ B)
      (markedPhysicalCofactorCoordinates_fintype hP hdis hZ A) _ _ ?_
    intro v u hu
    exact markedPhysicalScalarCofactorTerm_supported_lifts hP hdis c b a hd₀ hY hm₀ hD
      hbelow hgood h.2 hη ht S T hS hT hα hβ hu
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro v _
    have hv : MarkedPhysicalMarkingDistinct B := v.2.2.2.1
    have hban : MarkedPhysicalCrossBan B a := by
      by_contra hban
      obtain ⟨hgood,hne⟩ := (markedPhysicalPad_source_crossBan_iff hdis c b a).mp ⟨hv,hban⟩
      exact h ⟨fun ⟨j,hj⟩ => hgood j hj,hne⟩
    apply Finset.sum_eq_zero
    intro u _
    unfold markedPhysicalPadCofactorTerm
    rw [ite_eq_left hban]

end
end ArtinMatthews
