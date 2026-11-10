module

public import ArtinMatthews.SourceComparisonDyads
public import ArtinMatthews.SourceComparisonTripleMean
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Retain exactly the dyadic scales that can meet the compact product cutoff. -/

namespace ArtinMatthews

open Finset

noncomputable section

def sourceComparisonTripleDyadKey (v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (sourceComparisonDyadKey v.1, sourceComparisonDyadKey v.2.1, sourceComparisonDyadKey v.2.2)

def sourceComparisonProductScale (j : ℕ × ℕ × ℕ) : ℝ :=
  (sourceComparisonDyadScale j.1:ℝ)*sourceComparisonDyadScale j.2.1*sourceComparisonDyadScale j.2.2

def sourceComparisonProductBox (S G R : Finset ℕ) (j : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  sourceComparisonDyad S j.1 ×ˢ (sourceComparisonDyad G j.2.1 ×ˢ sourceComparisonDyad R j.2.2)

def sourceComparisonProductDyads (S G R : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  sourceComparisonDyadIndices S ×ˢ (sourceComparisonDyadIndices G ×ˢ sourceComparisonDyadIndices R)

def sourceComparisonOccupiedDyads (S G R : Finset ℕ) (a b Y : ℝ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (sourceComparisonProductDyads S G R).filter (fun j =>
    a*Y ≤ 8*sourceComparisonProductScale j ∧ sourceComparisonProductScale j ≤ b*Y)

theorem sourceComparisonProductBox_positions (S G R : Finset ℕ) (j : ℕ × ℕ × ℕ)
    (hS : ∀ p ∈ S, 0 < p) (hG : ∀ m ∈ G, 0 < m) (hR : ∀ n ∈ R, 0 < n)
    {v : ℕ × ℕ × ℕ} (hv : v ∈ sourceComparisonProductBox S G R j) :
    sourceComparisonProductScale j ≤ (sourceComparisonTriplePosition v:ℝ) ∧
      (sourceComparisonTriplePosition v:ℝ) ≤ 8*sourceComparisonProductScale j := by
  obtain ⟨hp, hm, hn⟩ := mem_product.mp hv |>.imp_right mem_product.mp
  obtain ⟨hpl,hpu⟩ := sourceComparisonDyad_bounds hp (hS _ (mem_filter.mp hp).1)
  obtain ⟨hml,hmu⟩ := sourceComparisonDyad_bounds hm (hG _ (mem_filter.mp hm).1)
  obtain ⟨hnl,hnu⟩ := sourceComparisonDyad_bounds hn (hR _ (mem_filter.mp hn).1)
  constructor
  · dsimp [sourceComparisonProductScale, sourceComparisonTriplePosition]
    push_cast
    gcongr <;> exact_mod_cast ‹_›
  · dsimp [sourceComparisonProductScale, sourceComparisonTriplePosition]
    push_cast
    rw [show 8*((sourceComparisonDyadScale j.1:ℝ)*sourceComparisonDyadScale j.2.1*
        sourceComparisonDyadScale j.2.2) =
        (2*(sourceComparisonDyadScale j.1:ℝ))*(2*sourceComparisonDyadScale j.2.1)*
          (2*sourceComparisonDyadScale j.2.2) by ring]
    gcongr <;> exact_mod_cast ‹_›

theorem sourceComparisonProductBox_positions_mem (S G R : Finset ℕ) (j : ℕ × ℕ × ℕ)
    (hS : ∀ p ∈ S, 0 < p) (hG : ∀ m ∈ G, 0 < m) (hR : ∀ n ∈ R, 0 < n)
    {v : ℕ × ℕ × ℕ} (hv : v ∈ sourceComparisonProductBox S G R j) :
    sourceComparisonTriplePosition v ∈ Ioc 0 ⌊8*sourceComparisonProductScale j⌋₊ := by
  have h := sourceComparisonProductBox_positions S G R j hS hG hR hv
  have hZ : 0 < sourceComparisonProductScale j := by
    dsimp [sourceComparisonProductScale, sourceComparisonDyadScale]
    positivity
  exact mem_Ioc.mpr ⟨by exact_mod_cast hZ.trans_le h.1,
    (Nat.le_floor_iff (by positivity)).mpr h.2⟩

theorem sourceComparisonOccupiedDyads_card_le (S G R : Finset ℕ) (a b Y : ℝ) :
    (sourceComparisonOccupiedDyads S G R a b Y).card ≤
      (sourceComparisonDyadIndices S).card*(sourceComparisonDyadIndices G).card*
        (sourceComparisonDyadIndices R).card := by
  have hsub : sourceComparisonOccupiedDyads S G R a b Y ⊆ sourceComparisonProductDyads S G R :=
    filter_subset _ _
  simpa only [sourceComparisonProductDyads, card_product, mul_assoc] using card_le_card hsub

/-- The literal product-cut sum partitions into finite dyadic boxes. Only
boxes disjoint from the support of the original smooth cutoff are omitted. -/
theorem sourceComparison_cutoff_product_dyads
    (S G R : Finset ℕ) (ψ : ℝ → ℂ) (c : ℕ × ℕ × ℕ → ℂ) (a b Y : ℝ)
    (hY : 0 < Y) (hψ : Function.support ψ ⊆ Set.Icc a b)
    (hS : ∀ p ∈ S, 0 < p) (hG : ∀ m ∈ G, 0 < m) (hR : ∀ n ∈ R, 0 < n) :
    (∑ v ∈ S×ˢ(G×ˢR), c v*ψ ((sourceComparisonTriplePosition v:ℝ)/Y)) =
      ∑ j ∈ sourceComparisonOccupiedDyads S G R a b Y,
        ∑ v ∈ sourceComparisonProductBox S G R j,
          c v*ψ ((sourceComparisonTriplePosition v:ℝ)/Y) := by
  classical
  let D := sourceComparisonProductDyads S G R
  let F (v : ℕ × ℕ × ℕ) := c v*ψ ((sourceComparisonTriplePosition v:ℝ)/Y)
  have hmap : ∀ v ∈ S×ˢ(G×ˢR), sourceComparisonTripleDyadKey v ∈ D := by
    intro v hv
    obtain ⟨hp, hm, hn⟩ := mem_product.mp hv |>.imp_right mem_product.mp
    exact mem_product.mpr ⟨mem_image_of_mem _ hp, mem_product.mpr
      ⟨mem_image_of_mem _ hm, mem_image_of_mem _ hn⟩⟩
  have hfiber (j : ℕ × ℕ × ℕ) :
      ((S×ˢ(G×ˢR)).filter (fun v => sourceComparisonTripleDyadKey v=j)) =
        sourceComparisonProductBox S G R j := by
    ext v
    rcases j with ⟨jp,jm,jn⟩
    simp only [mem_filter, mem_product, sourceComparisonTripleDyadKey, sourceComparisonProductBox,
      sourceComparisonDyad, Prod.mk.injEq]
    tauto
  have hsub : sourceComparisonOccupiedDyads S G R a b Y ⊆ D := filter_subset _ _
  change (∑ v ∈ S×ˢ(G×ˢR), F v) = _
  rw [← sum_fiberwise_of_maps_to hmap F]
  simp_rw [hfiber]
  symm
  apply sum_subset hsub
  intro j hj hnot
  apply sum_eq_zero
  intro v hv
  have hp := sourceComparisonProductBox_positions S G R j hS hG hR hv
  have hzero : ψ ((sourceComparisonTriplePosition v:ℝ)/Y) = 0 := by
    by_contra hne
    have hs : (sourceComparisonTriplePosition v:ℝ)/Y ∈ Set.Icc a b := hψ hne
    apply hnot
    exact mem_filter.mpr ⟨hj, ((le_div_iff₀ hY).mp hs.1).trans hp.2,
      hp.1.trans ((div_le_iff₀ hY).mp hs.2)⟩
  simp only [F, hzero, mul_zero]

end
end ArtinMatthews
