module

public import ArtinMatthews.GiantCandidateAllocationWeights
public import ArtinMatthews.GiantMarkedCharacterCriterion


set_option backward.privateInPublic true
@[expose] public section

/-! Exact allocation of the performed active one-mark term. The original
product cutoff, square condition, ordered slot factorial and fixed
character all persist in the resulting finite correlation. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateAllocation_marked_tuple_sum {ι : Type*} [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (hPC : univ.biUnion P ⊆ C)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {W z : ℝ} (hW : 0 ≤ W) (hPW : ∀ p ∈ univ.biUnion P, W < (p : ℝ))
    {M : ℕ} (χ : DirichletCharacter ℂ M) (j X : ℕ) (hj : 0 < j)
    (w : ℕ → ℂ) (q : ℝ) :
    (∑ t ∈ (giantOrderedProductTuples j X).filter
      (fun t => ∀ p ∈ C, ¬ p ^ 2 ∣ ∏ i, t i),
      let n := ∏ i, t i
      w n * (giantCandidateActiveOneMark P q (n-1) : ℂ) *
        ((∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient C W z (t i)) *
          (giantCandidateActiveOneMark P (q/(j:ℝ)) n : ℂ))) / j.factorial =
      ((j : ℂ) ^ Fintype.card ι / j.factorial) *
        ∑ n ∈ (Ioc 0 X).filter (fun n => ∀ p ∈ C, ¬ p ^ 2 ∣ n),
          w n * (giantCandidateActiveOneMark P q (n-1) : ℂ) * χ n *
            (giantCandidateActiveOneMark P q n : ℂ) *
              giantCandidateAllocationCore C (univ.biUnion P) W z j n := by
  classical
  let S := (giantOrderedProductTuples j X).filter
    (fun t => ∀ p ∈ C, ¬ p ^ 2 ∣ ∏ i, t i)
  let D := (Ioc 0 X).filter (fun n => ∀ p ∈ C, ¬ p ^ 2 ∣ n)
  let g (t : Fin j → ℕ) := ∏ i, t i
  let L (n : ℕ) : ℂ := giantCandidateActiveOneMark P q (n-1)
  let R (n : ℕ) : ℂ := giantCandidateActiveOneMark P (q/(j:ℝ)) n
  let F (t : Fin j → ℕ) := w (g t) * L (g t) *
    ((∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient C W z (t i)) * R (g t))
  let J := (j : ℂ) ^ Fintype.card ι
  let H (n : ℕ) := w n * L n * χ n * (giantCandidateActiveOneMark P q n : ℂ) *
    giantCandidateAllocationCore C (univ.biUnion P) W z j n
  have hg : ∀ t ∈ S, g t ∈ D := by
    intro t ht
    obtain ⟨htF, hsq⟩ := mem_filter.mp ht
    obtain ⟨hpos, hprod⟩ := mem_giantOrderedProductTuples.mp htF
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨prod_pos (fun i _ => hpos i), hprod⟩, hsq⟩
  have hfib (n : ℕ) (hn : n ∈ D) :
      S.filter (fun t => g t = n) = giantOrderedProductFiber j n := by
    ext t
    simp only [S, mem_filter, mem_giantOrderedProductTuples, mem_giantOrderedProductFiber]
    constructor
    · exact fun h => ⟨h.1.1.1,h.2⟩
    · rintro ⟨ht, hp⟩
      have hs := (mem_filter.mp hn).2
      have hN := (mem_Ioc.mp (mem_filter.mp hn).1).2
      exact ⟨⟨⟨ht, hp.le.trans hN⟩, fun p hpC hpd => hs p hpC (hp ▸ hpd)⟩, hp⟩
  have hinner (n : ℕ) (hn : n ∈ D) :
      (∑ t ∈ giantOrderedProductFiber j n,F t) = J * H n := by
    have hn0 := (mem_Ioc.mp (mem_filter.mp hn).1).1
    have hs := (mem_filter.mp hn).2
    calc
      _ = w n * L n *
        (∑ t ∈ giantOrderedProductFiber j n,
          (∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient C W z (t i)) * R n) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro t ht
        have hp : g t = n := (mem_giantOrderedProductFiber.mp ht).2
        dsimp only [F]
        rw [hp]
      _ = _ := by
        dsimp only [R, J, H]
        rw [giantCandidateAllocation_marked_fiber_sum C P hPC hP hdis hW hPW χ j hj hn0 (fun p hp => hs p (hPC hp)) q]
        ring
  change (∑ t ∈ S, F t) / j.factorial = (J / j.factorial) * ∑ n ∈ D, H n
  calc
    _ = (∑ n ∈ D, ∑ t ∈ S.filter (fun t => g t = n), F t) / j.factorial := by
      rw [sum_fiberwise_of_maps_to hg F]
    _ = (∑ n ∈ D,J * H n) / j.factorial := by
      apply congrArg (fun b : ℂ => b / j.factorial)
      exact sum_congr rfl (fun n hn => by rw [hfib n hn, hinner n hn])
    _ = _ := by rw [← Finset.mul_sum]; ring

def giantCandidateActualMarkedProxyTerm {J ι : Type*} [Fintype J] [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  (∑ t ∈ (giantOrderedProductTuples j ⌊T*x⌋₊).filter
      (fun t => ∀ p ∈ C, ¬ p ^ 2 ∣ ∏ i, t i),
      let n := ∏ i, t i
      markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
        (giantCandidateActiveOneMark P q (n-1) : ℂ) *
        ((∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient C
          (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) (t i)) *
            (giantCandidateActiveOneMark P (q/(j:ℝ)) n : ℂ))) / j.factorial

theorem giantCandidateActualMarkedProxyTerm_eq_allocated {J ι : Type*} [Fintype J] [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (hPC : univ.biUnion P ⊆ C)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (hj : 0 < j) (x : ℝ)
    (hPW : ∀ p ∈ univ.biUnion P, Real.exp ((Real.log x)^(6/25:ℝ)) < (p : ℝ)) :
    giantCandidateActualMarkedProxyTerm C P e χ ε Φ T γ q j x =
      ((j : ℂ) ^ Fintype.card ι / j.factorial) *
        ∑ n ∈ (Ioc 0 ⌊T*x⌋₊).filter (fun n => ∀ p ∈ C, ¬ p ^ 2 ∣ n),
          markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
            (giantCandidateActiveOneMark P q (n-1) : ℂ) * χ n *
            (giantCandidateActiveOneMark P q n : ℂ) *
              giantCandidateAllocationCore C (univ.biUnion P)
                (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n :=
  giantCandidateAllocation_marked_tuple_sum C P hPC hP hdis (Real.exp_nonneg _) hPW χ j
    ⌊T*x⌋₊ hj (markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x) q

end
end ArtinMatthews
