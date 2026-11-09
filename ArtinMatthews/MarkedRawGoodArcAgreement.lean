module

public import ArtinMatthews.MarkedMinorArcDirtyGoodCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Literal first/beta goodness is determined by its elementary arc truth
values. Finite failure probabilities introduce no additional ratio cuts. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPairBadRoots_congr_arcs (Q : Finset ℤ) (T : ℤ) (ε : ℝ)
    (r s : AddCircle (1:ℝ))
    (h : ∀ u ∈ Q,∀ v ∈ Q,u ≠ v →
      (r ∈ markedBadRootMultiple ((u-v)*T) ε ↔ s ∈ markedBadRootMultiple ((u-v)*T) ε)) :
    r ∈ markedPairBadRoots Q T ε ↔ s ∈ markedPairBadRoots Q T ε := by
  simp only [markedPairBadRoots,Set.mem_iUnion]
  constructor
  · rintro ⟨u,hu,v,hv,hm⟩
    refine ⟨u,hu,v,hv,?_⟩
    by_cases huv : u=v
    · simp only [ite_eq_left huv,Set.mem_empty_iff_false] at hm
    · rw [ite_eq_right huv] at hm ⊢
      exact (h u hu v hv huv).mp hm
  · rintro ⟨u,hu,v,hv,hm⟩
    refine ⟨u,hu,v,hv,?_⟩
    by_cases huv : u=v
    · simp only [ite_eq_left huv,Set.mem_empty_iff_false] at hm
    · rw [ite_eq_right huv] at hm ⊢
      exact (h u hu v hv huv).mpr hm

theorem markedPairFailureProbability_congr_arcs {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (ε : ℝ) (r s : AddCircle (1:ℝ))
    (h : ∀ i,∀ u ∈ Q,∀ v ∈ Q,u ≠ v →
      (r ∈ markedBadRootMultiple ((u-v)*T i) ε ↔ s ∈ markedBadRootMultiple ((u-v)*T i) ε)) :
    markedPairFailureProbability Q T w ε r = markedPairFailureProbability Q T w ε s := by
  unfold markedPairFailureProbability
  apply Finset.sum_congr rfl
  intro i _
  have hi := markedPairBadRoots_congr_arcs Q (T i) ε r s (h i)
  by_cases hr : r ∈ markedPairBadRoots Q (T i) ε
  · simp only [ite_eq_left hr,ite_eq_left (hi.mp hr)]
  · have hs : s ∉ markedPairBadRoots Q (T i) ε := fun h' => hr (hi.mpr h')
    simp only [ite_eq_right hr,ite_eq_right hs]

def MarkedRawCircleGood {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ) (θ : AddCircle (1:ℝ)) : Prop :=
  θ ∉ markedFirstBadRoots (fun o : markedRawDyadicOmissions a d₀ =>
      markedSourceCopiedProduct (markedRawNumericActive a) o.1) ⌊Y^(1/5:ℝ)⌋₊ (Y^(-7/10:ℝ)) ∧
    ∀ (I : Finset J) (j : J),j ∈ I → (∀ k ∈ I,e k ≤ e j) →
      ¬Real.exp (-((Real.log x)^(e j))/4) ≤
        markedPairFailureProbability (markedRawDirtyFullTrials e x a (I.erase j))
          (markedFreshIntegerProduct (fun k : ↥(Finset.univ \ I) => e k.1) x)
          (markedFreshHarmonicLaw (fun k : ↥(Finset.univ \ I) => e k.1) x)
          (100*Real.exp (-((Real.log x)^(e j)))) θ

theorem markedRawDirtyGood_iff_circle {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    MarkedRawDirtyGood e x r d₀ Y w s ↔ MarkedRawCircleGood e x s.2.1 d₀ Y
      (((markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1):ℝ):AddCircle (1:ℝ)) := Iff.rfl

structure MarkedRawGoodArcAgreement {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ)
    (r s : AddCircle (1:ℝ)) : Prop where
  first : ∀ o : markedRawDyadicOmissions a d₀,∀ l ∈ Finset.Icc 1 ⌊Y^(1/5:ℝ)⌋₊,
    (r ∈ markedBadRootMultiple ((markedSourceCopiedProduct (markedRawNumericActive a) o.1*l:ℕ):ℤ) (Y^(-7/10:ℝ)) ↔
      s ∈ markedBadRootMultiple ((markedSourceCopiedProduct (markedRawNumericActive a) o.1*l:ℕ):ℤ) (Y^(-7/10:ℝ)))
  beta : ∀ (I : Finset J) (j : J)
    (t : MarkedFreshPrimeTuple (fun k : ↥(Finset.univ \ I) => e k.1) x)
    (u v : ↥(markedRawDirtyFullTrials e x a (I.erase j))),
    (r ∈ markedBadRootMultiple ((u.1-v.1)*markedFreshIntegerProduct (fun k : ↥(Finset.univ \ I) => e k.1) x t)
        (100*Real.exp (-((Real.log x)^(e j)))) ↔
      s ∈ markedBadRootMultiple ((u.1-v.1)*markedFreshIntegerProduct (fun k : ↥(Finset.univ \ I) => e k.1) x t)
        (100*Real.exp (-((Real.log x)^(e j)))))

theorem markedRawCircleGood_congr_arcs {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ)
    (r s : AddCircle (1:ℝ)) (h : MarkedRawGoodArcAgreement e x a d₀ Y r s) :
    MarkedRawCircleGood e x a d₀ Y r ↔ MarkedRawCircleGood e x a d₀ Y s := by
  have hfirst : r ∈ markedFirstBadRoots (fun o : markedRawDyadicOmissions a d₀ =>
      markedSourceCopiedProduct (markedRawNumericActive a) o.1) ⌊Y^(1/5:ℝ)⌋₊ (Y^(-7/10:ℝ)) ↔
      s ∈ markedFirstBadRoots (fun o : markedRawDyadicOmissions a d₀ =>
      markedSourceCopiedProduct (markedRawNumericActive a) o.1) ⌊Y^(1/5:ℝ)⌋₊ (Y^(-7/10:ℝ)) := by
    simp only [markedFirstBadRoots,Set.mem_iUnion]
    constructor
    · rintro ⟨o,l,hl,hm⟩
      exact ⟨o,l,hl,(h.first o l hl).mp hm⟩
    · rintro ⟨o,l,hl,hm⟩
      exact ⟨o,l,hl,(h.first o l hl).mpr hm⟩
  have hprob (I : Finset J) (j : J) := markedPairFailureProbability_congr_arcs
    (markedRawDirtyFullTrials e x a (I.erase j))
    (markedFreshIntegerProduct (fun k : ↥(Finset.univ \ I) => e k.1) x)
    (markedFreshHarmonicLaw (fun k : ↥(Finset.univ \ I) => e k.1) x)
    (100*Real.exp (-((Real.log x)^(e j)))) r s
    (fun t u hu v hv _ => h.beta I j t ⟨u,hu⟩ ⟨v,hv⟩)
  unfold MarkedRawCircleGood
  simp only [hfirst,hprob]

end ArtinMatthews
