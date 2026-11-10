module

public import ArtinMatthews.SourceComparisonActualLowTime
public import ArtinMatthews.SourceComparisonSmallMarkReindex
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

/-! Splitting off a chosen small group preserves the literal endpoint.
The ordered slots are transported by their exact mark counts. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G H : Type*}

private def comparisonListEquiv (E : H ≃ G) (t : G → ℕ) (u : H → ℕ)
    (hu : ∀ h, t (E h) = u h) :
    ((g : G) → Fin (t g) → ℕ) ≃ ((h : H) → Fin (u h) → ℕ) :=
  (Equiv.piCongrLeft (fun g => Fin (t g) → ℕ) E).symm.trans
    (Equiv.piCongrRight fun h => (finCongr (hu h)).arrowCongr (Equiv.refl ℕ))

private theorem comparisonListEquiv_apply (E : H ≃ G) (t : G → ℕ) (u : H → ℕ)
    (hu : ∀ h, t (E h) = u h) (l : (g : G) → Fin (t g) → ℕ) (h : H) :
    comparisonListEquiv E t u hu l h = l (E h) ∘ (finCongr (hu h)).symm := rfl

private theorem comparisonListEquiv_symm_apply (E : H ≃ G) (t : G → ℕ) (u : H → ℕ)
    (hu : ∀ h, t (E h) = u h) (l : (h : H) → Fin (u h) → ℕ) (h : H) :
    (comparisonListEquiv E t u hu).symm l (E h) = l h ∘ finCongr (hu h) := by
  funext j
  have he := congrFun (congrFun ((comparisonListEquiv E t u hu).apply_symm_apply l) h)
    (finCongr (hu h) j)
  simpa only [comparisonListEquiv_apply, Function.comp_apply, Equiv.symm_apply_apply] using he

private theorem comparisonListEquiv_mem [Fintype G] [Fintype H]
    (E : H ≃ G) (t : G → ℕ) (u : H → ℕ) (hu : ∀ h, t (E h) = u h)
    (P : G → Finset ℕ) (P' : H → Finset ℕ) (hP : ∀ h, P (E h) = P' h)
    (l : (g : G) → Fin (t g) → ℕ) :
    l ∈ sourceComparisonMarkChoices P t ↔
      comparisonListEquiv E t u hu l ∈ sourceComparisonMarkChoices P' u := by
  rw [mem_sourceComparisonMarkChoices, mem_sourceComparisonMarkChoices]
  constructor
  · rintro ⟨hm, hi⟩
    refine ⟨?_, ?_⟩
    · intro h j
      rw [comparisonListEquiv_apply, Function.comp_apply, ← hP h]
      exact hm (E h) _
    · intro h
      rw [comparisonListEquiv_apply]
      exact (hi (E h)).comp (finCongr (hu h)).symm.injective
  · rintro ⟨hm, hi⟩
    refine ⟨?_, ?_⟩
    · intro g
      obtain ⟨h, rfl⟩ := E.surjective g
      intro j
      simpa only [comparisonListEquiv_apply, Function.comp_apply, Equiv.symm_apply_apply, ← hP h]
        using hm h (finCongr (hu h) j)
    · intro g
      obtain ⟨h, rfl⟩ := E.surjective g
      have he := comparisonListEquiv_symm_apply E t u hu (comparisonListEquiv E t u hu l) h
      rw [Equiv.symm_apply_apply] at he
      rw [he]
      exact (hi h).comp (finCongr (hu h)).injective

private theorem comparisonMarkWeight_reindex [Fintype G] [Fintype H]
    (E : H ≃ G) (t : G → ℕ) (u : H → ℕ) (hu : ∀ h, t (E h) = u h)
    (P : G → Finset ℕ) (P' : H → Finset ℕ) (hP : ∀ h, P (E h) = P' h)
    (q : G → ℝ) (q' : H → ℝ) (hq : ∀ h, q (E h) = q' h)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonMarkWeight P t q b n =
      sourceComparisonMarkWeight P' u q' (b ∘ (comparisonListEquiv E t u hu).symm) n := by
  have hmass : sourceComparisonMarkMass P t = sourceComparisonMarkMass P' u := by
    unfold sourceComparisonMarkMass
    symm
    exact Fintype.prod_equiv E _ _ (fun h => by rw [hP h, hu h])
  have hdamp : sourceComparisonMarkHitDamping P t q n = sourceComparisonMarkHitDamping P' u q' n := by
    unfold sourceComparisonMarkHitDamping
    symm
    exact Fintype.prod_equiv E _ _ (fun h => by rw [hP h, hu h, hq h])
  have hsum :
      (∑ l ∈ sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t, b l) =
        ∑ l ∈ sourceComparisonMarkChoices (fun h => activeDivisors (P' h) n) u,
          (b ∘ (comparisonListEquiv E t u hu).symm) l :=
    Finset.sum_equiv (comparisonListEquiv E t u hu)
      (comparisonListEquiv_mem E t u hu _ _ (fun h => by rw [hP h]))
      (fun l _ => by rw [Function.comp_apply, Equiv.symm_apply_apply])
  simp only [sourceComparisonMarkWeight, hmass, hdamp, hsum]

/-- The inherited embedding of all groups except the chosen one. -/
def sourceComparisonOtherGroupEmbedding {x : ℝ}
    (i : G ↪ GiantCandidateGroupIndex x) (g : G) :
    {j : G // j ≠ g} ↪ GiantCandidateGroupIndex x :=
  (Function.Embedding.subtype (fun j => j ≠ g)).trans i

theorem sourceComparisonOtherGroupEmbedding_outside {x : ℝ}
    (i : G ↪ GiantCandidateGroupIndex x) (g : G) (s : GiantCandidateSmallGroupIndex x)
    (hg : i g = Sum.inl s) :
    (Sum.inl s : GiantCandidateGroupIndex x) ∉ Set.range (sourceComparisonOtherGroupEmbedding i g) := by
  rintro ⟨j, hj⟩
  change i j.val = Sum.inl s at hj
  exact j.property (i.injective (hj.trans hg.symm))

/-- Extend the remaining list by the fixed value at the omitted slot.
The test is independent of this value in the distinguished reindex. -/
def sourceComparisonOtherMarkTest [DecidableEq G] (t : G → ℕ) (g : G)
    (b : ((j : G) → Fin (t j) → ℕ) → ℂ) (p : ℕ)
    (l : (j : {j : G // j ≠ g}) → Fin (t j) → ℕ) : ℂ :=
  b (fun j => if h : j = g then fun _ => p else l ⟨j, h⟩)

theorem sourceComparisonOtherMarkTest_norm_le [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (t : G → ℕ) (g : G) (ht : t g = 1)
    (b : ((j : G) → Fin (t j) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1)
    {p : ℕ} (hp : p ∈ P g)
    {l : (j : {j : G // j ≠ g}) → Fin (t j) → ℕ}
    (hl : l ∈ sourceComparisonMarkChoices (fun j : {j : G // j ≠ g} => P j) (fun j => t j)) :
    ‖sourceComparisonOtherMarkTest t g b p l‖ ≤ 1 := by
  unfold sourceComparisonOtherMarkTest
  have hl' := (mem_sourceComparisonMarkChoices (fun j : {j : G // j ≠ g} => P j)
    (fun j => t j) l).mp hl
  apply hb
  refine (mem_sourceComparisonMarkChoices P t _).mpr ⟨?_, ?_⟩
  · intro j k
    by_cases h : j = g
    · subst j
      simpa using hp
    · simpa only [dite_eq_right h] using hl'.1 ⟨j, h⟩ k
  · intro j
    by_cases h : j = g
    · subst j
      intro a c _
      exact (finCongr ht).injective (Subsingleton.elim _ _)
    · simpa only [dite_eq_right h] using hl'.2 ⟨j, h⟩

private def comparisonDistinguishedEquiv (g : G) [DecidableEq G] :
    (Unit ⊕ {j : G // j ≠ g}) ≃ G := by
  letI : Unique {j : G // j = g} :=
    { default := ⟨g, rfl⟩, uniq := fun j => Subtype.ext j.property }
  exact ((Equiv.ofUnique Unit {j : G // j = g}).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl (· = g))

theorem sourceComparisonMarkWeight_distinguish [Fintype G] [DecidableEq G]
    {x : ℝ} (i : G ↪ GiantCandidateGroupIndex x)
    (g : G) (s : GiantCandidateSmallGroupIndex x) (hg : i g = Sum.inl s)
    (t : G → ℕ) (ht : t g = 1) (q : G → ℝ)
    (b : ((j : G) → Fin (t j) → ℕ) → ℂ)
    (hb : ∀ l l', (∀ j, j ≠ g → l j = l' j) → b l = b l') (p n : ℕ) :
    let i' := sourceComparisonOtherGroupEmbedding i g
    let i'' := sourceComparisonDistinguishedGroupEmbedding s i'
      (sourceComparisonOtherGroupEmbedding_outside i g s hg)
    sourceComparisonMarkWeight (giantCandidateGroup x ∘ i) t q b n =
      sourceComparisonMarkWeight (giantCandidateGroup x ∘ i'')
        (Sum.elim (fun _ : Unit => 1) (fun j => t j))
        (Sum.elim (fun _ : Unit => q g) (fun j => q j))
        (fun l => sourceComparisonOtherMarkTest t g b p (fun j => l (.inr j))) n := by
  intro i' i''
  let E := comparisonDistinguishedEquiv g
  let u : Unit ⊕ {j : G // j ≠ g} → ℕ := Sum.elim (fun _ => 1) (fun j => t j)
  let q' : Unit ⊕ {j : G // j ≠ g} → ℝ := Sum.elim (fun _ => q g) (fun j => q j)
  let P := giantCandidateGroup x ∘ i
  let P' := giantCandidateGroup x ∘ i''
  have hu (j : Unit ⊕ {j : G // j ≠ g}) : t (E j) = u j := by
    rcases j with j | j
    · exact ht
    · rfl
  have hP (j : Unit ⊕ {j : G // j ≠ g}) : P (E j) = P' j := by
    rcases j with j | j
    · change giantCandidateGroup x (i g) = giantCandidateGroup x (.inl s)
      rw [hg]
    · rfl
  have hq (j : Unit ⊕ {j : G // j ≠ g}) : q (E j) = q' j := by
    rcases j with j | j <;> rfl
  have htest : b ∘ (comparisonListEquiv E t u hu).symm =
      fun l => sourceComparisonOtherMarkTest t g b p (fun j => l (.inr j)) := by
    funext l
    let l' : (j : {j : G // j ≠ g}) → Fin (t j) → ℕ := fun j => l (.inr j)
    change b ((comparisonListEquiv E t u hu).symm l) =
      b (fun j => if h : j = g then fun _ => p else l' ⟨j, h⟩)
    apply hb
    intro j hj
    rw [dite_eq_right hj]
    let j' : {j : G // j ≠ g} := ⟨j, hj⟩
    have he := comparisonListEquiv_symm_apply E t u hu l (Sum.inr j')
    change (comparisonListEquiv E t u hu).symm l j =
      l (.inr j') ∘ (finCongr (hu (Sum.inr j')) : Fin (t j) ≃ Fin (t j)) at he
    funext k
    have hk : (finCongr (hu (Sum.inr j')) : Fin (t j) ≃ Fin (t j)) k = k := Fin.ext rfl
    exact (congrFun he k).trans (congrArg (l (.inr j')) hk)
  rw [comparisonMarkWeight_reindex E t u hu P P' hP q q' hq b n, htest]

theorem sourceComparisonCenteredMellinSum_distinguish
    {J : Type*} [Fintype J] [Fintype G] [DecidableEq G]
    (e : J → ℝ) (ε x Y σ B : ℝ) (ψ : ℝ → ℂ)
    (i : G ↪ GiantCandidateGroupIndex x)
    (g : G) (s : GiantCandidateSmallGroupIndex x) (hg : i g = Sum.inl s)
    (t : G → ℕ) (ht : t g = 1) (q : G → ℝ)
    (b : ((j : G) → Fin (t j) → ℕ) → ℂ)
    (hb : ∀ l l', (∀ j, j ≠ g → l j = l' j) → b l = b l') (p : ℕ)
    (k : ℕ) [NeZero k] (h : ℤ) (τ : ℝ) :
    let i' := sourceComparisonOtherGroupEmbedding i g
    let i'' := sourceComparisonDistinguishedGroupEmbedding s i'
      (sourceComparisonOtherGroupEmbedding_outside i g s hg)
    sourceComparisonCenteredMellinSum e ε x Y σ B ψ (giantCandidateGroup x ∘ i) t q b k h τ =
      sourceComparisonCenteredMellinSum e ε x Y σ B ψ (giantCandidateGroup x ∘ i'')
        (Sum.elim (fun _ : Unit => 1) (fun j => t j))
        (Sum.elim (fun _ : Unit => q g) (fun j => q j))
        (fun l => sourceComparisonOtherMarkTest t g b p (fun j => l (.inr j))) k h τ := by
  intro i' i''
  unfold sourceComparisonCenteredMellinSum sourceComparisonCenteredEndpoint
  congr 1
  apply sum_congr rfl
  intro n _
  rw [sourceComparisonMarkWeight_distinguish i g s hg t ht q b hb p n]

end
end ArtinMatthews
