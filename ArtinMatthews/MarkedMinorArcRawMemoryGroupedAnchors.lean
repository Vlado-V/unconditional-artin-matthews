module

public import ArtinMatthews.MarkedMinorArcRawMemoryAnchors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual projective-anchor integration simultaneously in every group.
The test can couple all groups and indexed values can repeat freely. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact ordered anchored-batch integration for arbitrary coupled tests.
There is no extra projective-line probability in the particle measure. -/
theorem markedRawParticle_grouped_batch_hit_integral
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (d : J → ℕ)
    (f : ((j : J) → Fin (d j) → MarkedRawParticle (P j)) → ℂ) :
    (∑ a : (j : J) → Fin (d j) → MarkedRawParticle (P j),
      (∏ j,∏ i,ν j (a j i).1)*
        (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (a j i) then (1:ℂ) else 0)*f a)=
      ∑ births : (j : J) → Fin (d j) → ↥(P j),
        (∏ j,∏ i,ν j (births j i))*f (fun j => markedRawAnchoredBatch (P j) z hz (d j) (births j)) := by
  classical
  let E : ((j : J) → Fin (d j) → ↥(P j)) →
      ((j : J) → Fin (d j) → MarkedRawParticle (P j)) :=
    fun births j => markedRawAnchoredBatch (P j) z hz (d j) (births j)
  have hE : Function.Injective E := by
    intro a b hab
    funext j
    exact markedRawAnchoredBatch_injective (P j) z hz (d j) (congrFun hab j)
  have hRange (a : (j : J) → Fin (d j) → MarkedRawParticle (P j)) :
      (∃ births,E births=a) ↔ ∀ j i,MarkedRawParticleHits (P j) z hz (a j i) := by
    constructor
    · rintro ⟨births,rfl⟩ j i
      exact markedRawAnchoredParticle_hits (P j) _ z hz
    · intro h
      have hh (j : J) := (markedRawAnchoredBatch_range (P j) z hz (d j) (a j)).mpr (h j)
      choose births hb using hh
      exact ⟨births,funext hb⟩
  let W : ((j : J) → Fin (d j) → MarkedRawParticle (P j)) → ℂ := fun a =>
    (∏ j,∏ i,ν j (a j i).1)*
      (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (a j i) then (1:ℂ) else 0)*f a
  have hzero : ∀ a,(¬∃ births,E births=a) → W a=0 := by
    intro a hn
    have hh : ¬∀ j i,MarkedRawParticleHits (P j) z hz (a j i) := fun h => hn ((hRange a).mpr h)
    obtain ⟨j,hj⟩ := not_forall.mp hh
    obtain ⟨i,hi⟩ := not_forall.mp hj
    have hp : (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (a j i) then (1:ℂ) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j)
        (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [ite_eq_right hi]))
    dsimp only [W]
    rw [hp,mul_zero,zero_mul]
  change (∑ a,W a)=_
  calc
    _ = ∑ a ∈ Finset.univ.image E,W a := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      exact hzero a (fun ⟨births,hb⟩ => ha (Finset.mem_image.mpr ⟨births,Finset.mem_univ _,hb⟩))
    _ = ∑ births : (j : J) → Fin (d j) → ↥(P j),W (E births) :=
      Finset.sum_image (fun _ _ _ _ h => hE h)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro births _
      have hh : (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (E births j i) then (1:ℂ) else 0)=1 := by
        apply Finset.prod_eq_one
        intro j _
        apply Finset.prod_eq_one
        intro i _
        exact ite_eq_left (markedRawAnchoredParticle_hits (P j) _ z hz)
      dsimp only [W]
      rw [hh,mul_one]
      rfl

end ArtinMatthews
