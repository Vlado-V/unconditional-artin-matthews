module

public import ArtinMatthews.RoughBonferroniDivisors


set_option backward.privateInPublic true
@[expose] public section

/-! Exact support and divisor scale of the finite complex truncation. -/
namespace ArtinMatthews

/-- Prime subsets of size at most `r` have squarefree positive divisors,
bounded by `v^r` when every sieving prime is at most `v`. -/
theorem roughTruncationSubsets_support (P : Finset ℕ) (r v : ℕ)
    (hv : 1 ≤ v) (hprime : ∀ p ∈ P, p.Prime) (hheight : ∀ p ∈ P, p ≤ v)
    (S : Finset ℕ) (hS : S ∈ roughTruncationSubsets P r) :
    0 < roughSubsetDivisor S ∧ Squarefree (roughSubsetDivisor S) ∧
      roughSubsetDivisor S ≤ v ^ r := by
  have hSP : S ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hcard : S.card ≤ r := (Finset.mem_filter.mp hS).2
  refine ⟨roughSubsetDivisor_pos S (fun p hp => hprime p (hSP hp)), ?_⟩
  exact OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.coefficient_divisor_support P
    hv hprime hheight hcard (Finset.mem_powersetCard.mpr ⟨hSP, rfl⟩)

end ArtinMatthews
