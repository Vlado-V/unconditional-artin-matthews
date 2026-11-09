module

public import ArtinMatthews.GiantComparisonStripSum
public import ArtinMatthews.GiantTwoSidedSharedInvariant


set_option backward.privateInPublic true
@[expose] public section

/-! The original centered and allocation cores are invariant under the
variable-length copied product. All copied labels are units for the fixed
character at the actual large source scale. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantComparisonSharedProduct_invariant {J A : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} {C : J → Finset (Fin k)}
    (hP : ∀ j p, p ∈ P j → p.Prime) (c : GiantComparisonSharedLabels P C)
    (F : ℕ → A) (hF : ∀ j p, p ∈ P j → ∀ n : ℕ, 0 < n → F (p*n) = F n)
    {n : ℕ} (hn : 0 < n) : F (giantComparisonSharedProduct c*n) = F n := by
  let good (a : ℕ) := 0 < a ∧ ∀ v : ℕ, 0 < v → F (a*v) = F v
  have hmul (a b : ℕ) (ha : good a) (hb : good b) : good (a*b) := by
    refine ⟨Nat.mul_pos ha.1 hb.1, fun v hv => ?_⟩
    rw [Nat.mul_assoc, ha.2 _ (Nat.mul_pos hb.1 hv), hb.2 _ hv]
  have hone : good 1 := ⟨Nat.one_pos, fun v _ => by rw [Nat.one_mul]⟩
  have hprod : good (giantComparisonSharedProduct c) := by
    unfold giantComparisonSharedProduct
    apply prod_induction _ good hmul hone
    intro j _
    apply prod_induction _ good hmul hone
    intro i _
    exact ⟨(hP j _ (c j i).property).pos, hF j _ (c j i).property⟩
  exact hprod.2 n hn

theorem giantComparisonSharedProduct_coprime {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k m : ℕ} {C : J → Finset (Fin k)}
    (c : GiantComparisonSharedLabels P C) (hm : ∀ j p, p ∈ P j → p.Coprime m) :
    (giantComparisonSharedProduct c).Coprime m := by
  apply Nat.Coprime.prod_left
  intro j _
  apply Nat.Coprime.prod_left
  intro i _
  exact hm j _ (c j i).property

theorem giantCandidateComparisonSharedInvariant_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    (m : ℕ) (hm : 0 < m) (γ : ℝ) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) (k : ℕ)
      (C : S → Finset (Fin k)),
      let P (g : S) := giantCandidateGroup x g.val
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      ∀ (c : GiantComparisonSharedLabels P C) (n : ℕ), 0 < n →
        F (giantComparisonSharedProduct c*n) = F n ∧
        G (giantComparisonSharedProduct c*n) = G n ∧
        (giantComparisonSharedProduct c).Coprime m := by
  filter_upwards [giantCandidateFirstEndpoint_active_invariant_eventually e he hεq,
    giantCandidateFullPrimes_coprime_modulus_eventually m hm,
    eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hf hc hx hL
  intro S k C
  let P (g : S) := giantCandidateGroup x g.val
  let F := giantCandidateFirstEndpoint e ε x
  let U := univ.biUnion P
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) U
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  dsimp only
  intro c n hn
  have hmem (g : S) (p : ℕ) (hp : p ∈ P g) : p ∈ giantCandidateFullPrimes x :=
    mem_giantCandidateFullPrimes.mpr ⟨g.val,hp⟩
  have hP (g : S) (p : ℕ) (hp : p ∈ P g) : p.Prime :=
    (giantCandidateFullPrimes_range hx hL (hmem g p hp)).1
  have hF (g : S) (p : ℕ) (hp : p ∈ P g) (v : ℕ) : F (p*v) = F v := by
    obtain ⟨hprime,hlo,hhi⟩ := giantCandidateFullPrimes_range hx hL (hmem g p hp)
    apply hf p hprime _ _ v
    · exact (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))).trans hlo
    · exact hhi.le.trans (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)))
  have hG (g : S) (p : ℕ) (hp : p ∈ P g) (v : ℕ) (hv : 0 < v) : G (p*v) = G v := by
    have hU : p ∈ U := mem_biUnion.mpr ⟨g,mem_univ _,hp⟩
    unfold G giantCandidateAllocationCore
    rw [giantCandidateStrip_mul_prime U (hP g p hp) hU hv]
  exact ⟨giantComparisonSharedProduct_invariant hP c F (fun g p hp v _ => hF g p hp v) hn,
    giantComparisonSharedProduct_invariant hP c G hG hn,
    giantComparisonSharedProduct_coprime c (fun g p hp => hc p (hmem g p hp))⟩

end
end ArtinMatthews
