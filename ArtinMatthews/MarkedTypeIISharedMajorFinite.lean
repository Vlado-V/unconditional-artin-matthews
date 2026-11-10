module

public import ArtinMatthews.MarkedTypeIIScalarMajorMass
public import ArtinMatthews.MarkedTypeIISharedLabelSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact scalar major sums on subsets of the literal label pair carrier.
The shared-label remainder has its own absolute estimate, with every
endpoint and dyadic factor retained in the summand. -/
namespace ArtinMatthews
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset ℕ)

def markedTypeIIScalarMajorOn
    (L : Finset (ℕ×ℕ)) (S T N : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ)
    (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ) : ℂ :=
  (markedMajorLabelMass P:ℂ)^2 *
    ∑ z ∈ L, ∑ v ∈ S×ˢN, ∑ w ∈ T×ˢN,
      G z v w * markedTypeIIScalarMajorTerm η ψ Q Y α β z.1 z.2 v w

theorem markedTypeIIScalarMajorOn_split
    (L : Finset (ℕ×ℕ)) (E : (ℕ×ℕ) → Prop) (S T N : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ)
    (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ) :
    markedTypeIIScalarMajorOn P L S T N η ψ Q Y α β G =
      markedTypeIIScalarMajorOn P (L.filter E) S T N η ψ Q Y α β G +
      markedTypeIIScalarMajorOn P (L.filter fun z => ¬ E z) S T N η ψ Q Y α β G := by
  unfold markedTypeIIScalarMajorOn
  rw [← mul_add, sum_filter_add_sum_filter_not]

theorem markedTypeIIScalarMajorOn_dyad
    (S T N : Finset ℕ) (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ)
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4)
    (α β : ℕ → ℂ) (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ) :
    markedTypeIIScalarMajorOn P (markedMajorLabelSet P×ˢmarkedMajorLabelSet P)
      S T N η ψ Q Y α β G =
    markedTypeIIScalarMajorOn P (markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y)
      S T N η ψ Q Y α β G := by
  unfold markedTypeIIScalarMajorOn
  apply congrArg (fun x : ℂ => (markedMajorLabelMass P:ℂ)^2*x)
  symm
  apply sum_subset
  · intro z hz
    obtain ⟨hb,ha⟩ := mem_product.mp hz
    exact mem_product.mpr ⟨(mem_filter.mp hb).1,(mem_filter.mp ha).1⟩
  · intro z hz hd
    obtain ⟨hb,ha⟩ := mem_product.mp hz
    have hp (b : ℕ) (hb : b ∈ markedMajorLabelSet P) (hn : η ((b:ℝ)/Y)≠0) :
        b ∈ markedTypeIIDyadLabels P Y := by
      obtain ⟨hlo,hhi⟩ := hη hn
      refine mem_filter.mpr ⟨hb,?_⟩
      exact ⟨by simpa only [one_mul] using (le_div_iff₀ hY).mp hlo,(div_le_iff₀ hY).mp hhi⟩
    apply sum_eq_zero
    intro v _
    apply sum_eq_zero
    intro w _
    by_cases hηb : η ((z.1:ℝ)/Y)=0
    · simp only [markedTypeIIScalarMajorTerm,hηb,zero_mul,mul_zero]
    · have hηa : η ((z.2:ℝ)/Y)=0 := by
        by_contra h
        exact hd (mem_product.mpr ⟨hp _ hb hηb,hp _ ha h⟩)
      simp only [markedTypeIIScalarMajorTerm,hηa,mul_zero,zero_mul]

theorem markedTypeIIScalarMajorOn_label_sum
    (S T N : Finset ℕ) (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ)
    (α β : ℕ → ℂ) (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ) :
    markedTypeIIScalarMajorOn P (markedMajorLabelSet P×ˢmarkedMajorLabelSet P)
        S T N η ψ Q Y α β G =
      (markedMajorLabelMass P:ℂ)^2 *
        ∑ b ∈ markedMajorLabelSet P, ∑ m ∈ S, ∑ n ∈ N,
        ∑ a ∈ markedMajorLabelSet P, ∑ r ∈ T, ∑ s ∈ N,
          G (b,a) (m,n) (r,s)*markedTypeIIScalarMajorTerm η ψ Q Y α β b a (m,n) (r,s) := by
  simp only [markedTypeIIScalarMajorOn,sum_product]
  apply congrArg (fun x : ℂ => (markedMajorLabelMass P:ℂ)^2*x)
  apply sum_congr rfl
  intro b _
  rw [sum_comm (s := markedMajorLabelSet P) (t := S)]
  apply sum_congr rfl
  intro m _
  rw [sum_comm (s := markedMajorLabelSet P) (t := N)]

theorem markedTypeIIScalarMajorOn_norm_le
    (L : Finset (ℕ×ℕ)) (S T N : Finset ℕ) (Z : ℕ)
    (hS : ∀ v ∈ S×ˢN, v.1*v.2 ∈ Icc 1 Z)
    (hT : ∀ v ∈ T×ˢN, v.1*v.2 ∈ Icc 1 Z)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) {Q Y R W A B : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : ∀ u, ‖η u‖ ≤ 1) (hψ : ∀ u, ‖ψ u‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (α β : ℕ → ℂ) (hαS : ∀ m ∈ S, ‖α m‖ ≤ A) (hαT : ∀ m ∈ T, ‖α m‖ ≤ A)
    (hβ : ∀ n ∈ N, ‖β n‖ ≤ B)
    (hL : L ⊆ markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y)
    (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ)
    (hG : ∀ z ∈ L, ∀ v ∈ S×ˢN, ∀ w ∈ T×ˢN, ‖G z v w‖ ≤ 1) :
    ‖markedTypeIIScalarMajorOn P L S T N η ψ Q Y α β G‖ ≤
      (markedMajorLabelMass P)^2*(L.card:ℝ)*(((A*B)^2*W*(4*Q^3/Y))*
        ((2*R+1)*(Z:ℝ)*(∑ d ∈ Icc 1 Z,1/(d:ℝ))^3)) := by
  let C := ((A*B)^2*W*(4*Q^3/Y))*((2*R+1)*(Z:ℝ)*(∑ d ∈ Icc 1 Z,1/(d:ℝ))^3)
  unfold markedTypeIIScalarMajorOn
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ z ∈ L, C := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro z hz
      obtain ⟨hb,ha⟩ := mem_product.mp (hL hz)
      have hbY := (mem_filter.mp hb).2.1
      have haY := (mem_filter.mp ha).2.1
      apply (norm_sum_le _ _).trans
      apply (sum_le_sum (fun v _ => norm_sum_le _ _)).trans
      exact markedTypeIIScalarMajorPair_abs_le S T N Z hS hT η ψ hQ hY hR hW hA hB
        hη hψ hsupp α β hαS hαT hβ z.1 z.2 hbY haY (G z) (hG z hz)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,C]

theorem markedTypeIIScalarMajor_shared_norm_le
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (S T N : Finset ℕ) (Z : ℕ)
    (hS : ∀ v ∈ S×ˢN, v.1*v.2 ∈ Icc 1 Z)
    (hT : ∀ v ∈ T×ˢN, v.1*v.2 ∈ Icc 1 Z)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) {Q Y R W A B : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : ∀ u, ‖η u‖ ≤ 1) (hψ : ∀ u, ‖ψ u‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (α β : ℕ → ℂ) (hαS : ∀ m ∈ S, ‖α m‖ ≤ A) (hαT : ∀ m ∈ T, ‖α m‖ ≤ A)
    (hβ : ∀ n ∈ N, ‖β n‖ ≤ B)
    (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ)
    (hG : ∀ z v w, ‖G z v w‖ ≤ 1) :
    ‖markedTypeIIScalarMajorOn P
        ((markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter fun z => ¬ z.1.Coprime z.2)
        S T N η ψ Q Y α β G‖ ≤
      64*(markedMajorLabelMass P)^2*(A*B)^2*W*(2*R+1)*Q^3*Y*(Z:ℝ)*
        (∑ d ∈ Icc 1 Z,1/(d:ℝ))^3*(∑ p ∈ Finset.univ.biUnion P,1/(p:ℝ)^2) := by
  let C := ((A*B)^2*W*(4*Q^3/Y))*((2*R+1)*(Z:ℝ)*(∑ d ∈ Icc 1 Z,1/(d:ℝ))^3)
  let L := (markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter (fun z => ¬ z.1.Coprime z.2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  calc
    _ ≤ (markedMajorLabelMass P)^2*(L.card:ℝ)*C :=
      markedTypeIIScalarMajorOn_norm_le P L S T N Z hS hT η ψ hQ hY hR hW hA hB
        hη hψ hsupp α β hαS hαT hβ (filter_subset _ _) G (fun z _ v _ w _ => hG z v w)
    _ ≤ (markedMajorLabelMass P)^2*((4*Y)^2 * ∑ p ∈ Finset.univ.biUnion P,1/(p:ℝ)^2)*C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (markedTypeIISharedDyadLabels_card_le P hP Y hY) (sq_nonneg _)) hC
    _ = _ := by
      dsimp only [C]
      field_simp [hY.ne']
      ring

end
end ArtinMatthews
