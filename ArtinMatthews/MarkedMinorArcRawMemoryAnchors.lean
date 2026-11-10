module

public import ArtinMatthews.MarkedMinorArcRawGhostState
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

/-! Actual counting-measure projective anchors in the finite Fock measure.
Restricting particles to hit the current line leaves exactly the tilted
prime integration, with no further factor 1/(p+1). -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Attaching the actual current anchor never identifies different primes. -/
theorem markedRawAnchoredParticle_injective (P : Finset Nat.Primes) (z : ℤ × ℤ)
    (hz : IsCoprime z.1 z.2) : Function.Injective (fun p : P => markedRawAnchoredParticle P p z hz) := by
  intro p q hpq
  exact congrArg Sigma.fst hpq

/-- Literal one-particle hit integration selects its unique current anchor;
there is no uniform projective-line normalization in the particle measure. -/
theorem markedRawParticle_hit_integral (P : Finset Nat.Primes) (ν : P → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (f : MarkedRawParticle P → ℂ) :
    (∑ a : MarkedRawParticle P, ν a.1*(if MarkedRawParticleHits P z hz a then 1 else 0)*f a)=
      ∑ p : P, ν p*f (markedRawAnchoredParticle P p z hz) := by
  classical
  simp only [← Finset.univ_sigma_univ,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  let anchor : MarkedRawPrimeLine p.1 := markedPrimePositionLine (p.1 : ℕ) z hz
  change (∑ l : MarkedRawPrimeLine p.1, ν p*(if l=anchor then 1 else 0)*f ⟨p,l⟩)=_
  calc
    _ = ν p*(if anchor=anchor then 1 else 0)*f ⟨p,anchor⟩ := by
      apply Fintype.sum_eq_single anchor
      intro l hl
      rw [ite_eq_right hl,mul_zero,zero_mul]
    _ = _ := by rw [ite_eq_left rfl,mul_one]; rfl

/-- The literal ordered anchored birth batch. Prime repetitions remain
possible and every actual batch index is retained. -/
def markedRawAnchoredBatch (P : Finset Nat.Primes) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (d : ℕ) (births : Fin d → P) : Fin d → MarkedRawParticle P :=
  fun i => markedRawAnchoredParticle P (births i) z hz

theorem markedRawAnchoredBatch_injective (P : Finset Nat.Primes) (z : ℤ × ℤ)
    (hz : IsCoprime z.1 z.2) (d : ℕ) : Function.Injective (markedRawAnchoredBatch P z hz d) := by
  intro a b hab
  funext i
  exact markedRawAnchoredParticle_injective P z hz (congrFun hab i)

/-- The actual batch lies in the anchor image exactly when all of its
indexed particles hit, including any repeated prime-and-anchor values. -/
theorem markedRawAnchoredBatch_range (P : Finset Nat.Primes) (z : ℤ × ℤ)
    (hz : IsCoprime z.1 z.2) (d : ℕ) (a : Fin d → MarkedRawParticle P) :
    (∃ births, markedRawAnchoredBatch P z hz d births=a) ↔
      ∀ i, MarkedRawParticleHits P z hz (a i) := by
  constructor
  · rintro ⟨births,rfl⟩ i
    exact markedRawAnchoredParticle_hits P _ z hz
  · intro hh
    refine ⟨fun i => (a i).1,?_⟩
    funext i
    have hi := hh i
    cases ha : a i with
    | mk p l =>
      change markedRawAnchoredParticle P ((a i).1) z hz=⟨p,l⟩
      rw [ha]
      rw [ha] at hi
      have hh' : l=markedPrimePositionLine (p.1 : ℕ) z hz := hi
      exact congrArg (Sigma.mk p) hh'.symm

/-- Exact ordered-batch hit integration with the actual particle measure.
This is the anchor step in the unordered ghost factorial adjoint. -/
theorem markedRawParticle_batch_hit_integral (P : Finset Nat.Primes) (ν : P → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (d : ℕ)
    (f : (Fin d → MarkedRawParticle P) → ℂ) :
    (∑ a : Fin d → MarkedRawParticle P,
      (∏ i, ν (a i).1)*(∏ i, if MarkedRawParticleHits P z hz (a i) then (1:ℂ) else 0)*f a)=
      ∑ births : Fin d → P, (∏ i, ν (births i))*f (markedRawAnchoredBatch P z hz d births) := by
  classical
  let E := markedRawAnchoredBatch P z hz d
  have hE := markedRawAnchoredBatch_injective P z hz d
  let W : (Fin d → MarkedRawParticle P) → ℂ := fun a =>
    (∏ i, ν (a i).1)*(∏ i, if MarkedRawParticleHits P z hz (a i) then (1:ℂ) else 0)*f a
  have hzero : ∀ a, (¬∃ births, E births=a) → W a=0 := by
    intro a hn
    have hh : ¬∀ i, MarkedRawParticleHits P z hz (a i) :=
      fun h => hn ((markedRawAnchoredBatch_range P z hz d a).mpr h)
    obtain ⟨i,hi⟩ := not_forall.mp hh
    have hp : (∏ i, if MarkedRawParticleHits P z hz (a i) then (1:ℂ) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [ite_eq_right hi])
    dsimp only [W]
    rw [hp,mul_zero,zero_mul]
  change (∑ a, W a)=_
  calc
    _ = ∑ a ∈ Finset.univ.image E, W a := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      exact hzero a (fun ⟨births,hb⟩ => ha (Finset.mem_image.mpr ⟨births,Finset.mem_univ _,hb⟩))
    _ = ∑ births : Fin d → P, W (E births) := Finset.sum_image (fun _ _ _ _ h => hE h)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro births _
      simp only [W,E,markedRawAnchoredBatch,markedRawAnchoredParticle,MarkedRawParticleHits,
        ite_true,Finset.prod_const_one,mul_one]

end ArtinMatthews
