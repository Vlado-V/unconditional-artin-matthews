module

public import ArtinMatthews.GiantTwoSidedRawKernel
public import ArtinMatthews.GiantCandidateSelectedGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The literal candidate cores and fixed character discharge every
arithmetic premise of the shared-product reindexing. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateRawPhysical_sum_eq_shared_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (γ : ℝ) (j : ℕ)
    (q : ℝ) (Ψ : ℝ → ℂ) :
    ∀ᶠ x : ℝ in atTop,∀ (S : Finset (GiantCandidateGroupIndex x)) (k N : ℕ)
      (Z Z' : Finset ℕ), Z ⊆ Ioc 0 N →
      let P (i : S) := giantCandidateGroup x i.val
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      (∑ r : GiantTwoSidedRawPhysicalEdge P k Z Z',giantTwoSidedRawPhysicalTerm x q Ψ χ F G r) =
        ∑ a : GiantTwoSidedRawSharedEdge P k N Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a := by
  filter_upwards [giantCandidateRawSharedEndpointInvariant_eventually e he hεq m hm γ j,
    giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually,
    eventually_gt_atTop (0:ℝ)] with x hi hg hp hx
  intro S k N Z Z' hZ
  let P (i : S) := giantCandidateGroup x i.val
  have hP (i : S) (p : ℕ) (h : p∈P i) : p.Prime :=
    (hp p (mem_giantCandidateFullPrimes.mpr ⟨i.val,h⟩)).1
  exact giantTwoSidedRawPhysical_sum_eq_shared hP (hg S).1 hZ hx q Ψ χ _ _
    (fun c w hw => (hi S k c w hw).1) (fun c w hw => (hi S k c w hw).2.1)
    (fun c => (hi S k c 1 Nat.one_pos).2.2)

end
end ArtinMatthews
