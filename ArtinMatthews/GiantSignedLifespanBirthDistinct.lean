module

public import ArtinMatthews.GiantSignedChronologicalLifetime
public import ArtinMatthews.GiantPrimeLifespanStatus
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

/-! The decoded lifespan start fixes the unique operation of each
performed birth. Ordered local slot injectivity then gives the actual
global distinct-birth indicator. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

local notation "BirthData" => giantSignedChronologicalBirthData h
local notation "Birth" => GiantSignedPerformedBirth BirthData
local notation "Prime" => giantSignedPerformedBirthPrime BirthData
local notation "Group" => giantSignedPerformedBirthGroup (h := h)
local notation "Time" => giantSignedPerformedBirthTime BirthData

theorem giantSignedPerformedBirth_eq_of_group_time_prime
    (hfirst : ∀ g, Function.Injective ((h.state 0).2.1 g))
    (hfree : ∀ i g, Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g))
    (hborn : ∀ i g, Function.Injective (h.born i g))
    (a b : Birth) (hg : Group a = Group b) (ht : Time a = Time b) (hp : Prime a = Prime b) : a = b := by
  rcases a with ⟨g,j⟩ | (⟨i,g,j⟩ | ⟨i,g,j⟩) <;>
    rcases b with ⟨g',j'⟩ | (⟨i',g',j'⟩ | ⟨i',g',j'⟩)
  all_goals simp only [giantSignedPerformedBirthTime] at ht
  all_goals try omega
  · change g = g' at hg
    subst g'
    have he : j = j' := hfirst g (Subtype.ext hp)
    rw [he]
  · have hi : i = i' := Fin.ext (by omega)
    change g = g' at hg
    subst i'
    subst g'
    have hj : j.val = j'.val := hfree i g (Subtype.ext hp)
    have he : j = j' := Subtype.ext hj
    rw [he]
  · have hi : i = i' := Fin.ext (by omega)
    change g = g' at hg
    subst i'
    subst g'
    have he : j = j' := hborn i g (Subtype.ext hp)
    rw [he]

private theorem freshAt_view {A : Finset (Fin (n+1))} (c : GiantSignedResidueLifespanChoice A)
    (i : Fin (n+1)) (hi : giantSignedPrimeFreshAt c i) :
    ∃ L, giantSignedPrimeLifespanView A c = some L ∧ L.start = i ∧ L.ghostBirth ≠ true := by
  unfold giantSignedPrimeFreshAt at hi
  cases hv : giantSignedPrimeLifespanView A c with
  | none => exact False.elim (by simpa only [hv,Option.elim_none] using hi)
  | some L =>
    have hL : L.start = i ∧ i ∈ A := by simpa only [hv,Option.elim_some] using hi
    exact ⟨L,rfl,hL.1,fun hb => L.ghostBirth_iff.mp hb (hL.1.symm ▸ hL.2)⟩

private theorem ghostAt_view {A : Finset (Fin (n+1))} (c : GiantSignedResidueLifespanChoice A)
    (i : Fin (n+1)) (hi : giantSignedPrimeGhostBirthAt c i) :
    ∃ L, giantSignedPrimeLifespanView A c = some L ∧ L.start = i ∧ L.ghostBirth = true := by
  unfold giantSignedPrimeGhostBirthAt at hi
  cases hv : giantSignedPrimeLifespanView A c with
  | none => exact False.elim (by simpa only [hv,Option.elim_none] using hi)
  | some L => exact ⟨L,rfl,by simpa only [hv,Option.elim_some] using hi⟩

theorem giantSignedLifespanBirthDistinct {A : ∀ g, PB g → Finset (Fin (n+1))}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))
    (hdis : Pairwise (fun g g' => Disjoint (PB g) (PB g')))
    (hfirst : ∀ g, Function.Injective ((h.state 0).2.1 g))
    (hfree : ∀ i g, Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g))
    (hborn : ∀ i g, Function.Injective (h.born i g))
    (hInitial : ∀ g j, giantSignedPrimeFreshAt (c g ((h.state 0).2.1 g j)) 0)
    (hEdge : ∀ i g j, j ∉ (h.edge i).2.1 g → giantSignedPrimeFreshAt
      (c g (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g j)) i.succ)
    (hGhost : ∀ i g j, giantSignedPrimeGhostBirthAt (c g (h.born i g j)) i) :
    GiantSignedBirthDistinct BirthData := by
  classical
  let choose (a : Birth) := c (Group a) ⟨Prime a,giantSignedPerformedBirthPrime_mem_group a⟩
  have ht (a : Birth) : ∃ L, giantSignedPrimeLifespanView _ (choose a) = some L ∧
      Time a = 2*L.start.val + if L.ghostBirth = true then 1 else 0 := by
    rcases a with ⟨g,j⟩ | (⟨i,g,j⟩ | ⟨i,g,j⟩)
    · obtain ⟨L,hL,hstart,hflag⟩ := freshAt_view _ 0 (hInitial g j)
      refine ⟨L,hL,?_⟩
      rw [ite_eq_right hflag,hstart]
      simp only [giantSignedPerformedBirthTime,Fin.val_zero,Nat.mul_zero,Nat.add_zero]
    · obtain ⟨L,hL,hstart,hflag⟩ := freshAt_view _ i.succ (hEdge i g j.val j.property)
      refine ⟨L,hL,?_⟩
      rw [ite_eq_right hflag,hstart]
      simp only [giantSignedPerformedBirthTime,Fin.val_succ,Nat.add_zero]
      omega
    · obtain ⟨L,hL,hstart,hflag⟩ := ghostAt_view _ i (hGhost i g j)
      exact ⟨L,hL,by simp only [giantSignedPerformedBirthTime,hstart,hflag,ite_true]⟩
  intro a b hp
  have hg : Group a = Group b := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdis hne) (hp ▸ giantSignedPerformedBirthPrime_mem_group a)
      (giantSignedPerformedBirthPrime_mem_group b)
  let index (x : Birth) : Σ g, PB g := ⟨Group x,Prime x,giantSignedPerformedBirthPrime_mem_group x⟩
  have index_ext (x y : Σ g, PB g) (hgroup : x.1 = y.1) (hprime : x.2.val = y.2.val) : x = y := by
    obtain ⟨g,p⟩ := x
    obtain ⟨g',p'⟩ := y
    dsimp only at hgroup hprime
    subst g'
    exact congrArg (Sigma.mk g) (Subtype.ext hprime)
  have hindex : index a = index b := index_ext (index a) (index b) hg hp
  let code (x : Σ g, PB g) : ℕ := (giantSignedPrimeLifespanView _ (c x.1 x.2)).elim 0
    (fun L => 2*L.start.val + if L.ghostBirth = true then 1 else 0)
  have hcode (x : Birth) : Time x = code (index x) := by
    obtain ⟨L,hL,hT⟩ := ht x
    change Time x = (giantSignedPrimeLifespanView _ (choose x)).elim 0 _
    rw [hL,Option.elim_some]
    exact hT
  have ht_eq : Time a = Time b := (hcode a).trans ((congrArg code hindex).trans (hcode b).symm)
  exact giantSignedPerformedBirth_eq_of_group_time_prime h hfirst hfree hborn a b hg ht_eq hp

end
end ArtinMatthews
