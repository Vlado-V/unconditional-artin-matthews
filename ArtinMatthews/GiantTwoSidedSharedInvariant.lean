module

public import ArtinMatthews.GiantTwoSidedSharedLists
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateSelectedGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual invariant cores strip every shared label, while the
fixed-character phase uses the genuine coprimality of the whole list. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

private theorem giantTwoSided_product_invariant {I A : Type*} (S : Finset I)
    (a : I → ℕ) (ha : ∀ i ∈ S,0 < a i) (F : ℕ → A)
    (hF : ∀ i ∈ S,∀ n : ℕ,0 < n → F (a i*n)=F n)
    {n : ℕ} (hn : 0 < n) : F ((∏ i ∈ S,a i)*n)=F n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hsub (l : I) (hl : l ∈ S) : l ∈ insert i S := mem_insert_of_mem hl
    have hpos : 0 < (∏ l ∈ S,a l)*n :=
      Nat.mul_pos (prod_pos (fun l hl => ha l (hsub l hl))) hn
    rw [prod_insert hi,mul_assoc,hF i (mem_insert_self _ _) _ hpos]
    exact ih (fun l hl => ha l (hsub l hl)) (fun l hl => hF l (hsub l hl))

theorem giantTwoSidedSharedProduct_invariant {J A : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ i p,p∈P i → p.Prime)
    {k : ℕ} (c : MarkedPhysicalMarking P k) (F : ℕ → A)
    (hF : ∀ i p,p∈P i → ∀ n : ℕ,0 < n → F (p*n)=F n)
    {n : ℕ} (hn : 0 < n) :
    F (markedPhysicalMarkingProduct c*n)=F n := by
  rw [markedPhysicalMarkingProduct,← Fintype.prod_prod_type (fun z : J×Fin k => (c z.1 z.2:ℕ))]
  exact giantTwoSided_product_invariant univ (fun z : J×Fin k => (c z.1 z.2:ℕ))
    (fun z _ => (hP z.1 _ (c z.1 z.2).property).pos) F
    (fun z _ => hF z.1 _ (c z.1 z.2).property) hn

theorem giantCandidateRawSharedEndpointInvariant_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,e i ≤ 1/5) {ε : ℝ} (hεq : ε < 1/4)
    (m : ℕ) (hm : 0 < m) (γ : ℝ) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ (S : Finset (GiantCandidateGroupIndex x)) (k : ℕ),
      let P (i : S) := giantCandidateGroup x i.val
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      ∀ (c : MarkedPhysicalMarking P k) (n : ℕ),0 < n →
        F (markedPhysicalMarkingProduct c*n)=F n ∧
        G (markedPhysicalMarkingProduct c*n)=G n ∧
        (markedPhysicalMarkingProduct c).Coprime m := by
  filter_upwards [giantCandidateFirstEndpoint_active_invariant_eventually e he hεq,
    giantCandidateFullPrimes_coprime_modulus_eventually m hm,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hf hc hx hL
  intro S k
  let P (i : S) := giantCandidateGroup x i.val
  let F := giantCandidateFirstEndpoint e ε x
  let U := univ.biUnion P
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) U
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  dsimp only
  intro c n hn
  have hmem (i : S) (p : ℕ) (hp : p∈P i) : p∈giantCandidateFullPrimes x :=
    mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩
  have hP (i : S) (p : ℕ) (hp : p∈P i) : p.Prime :=
    (giantCandidateFullPrimes_range hx hL (hmem i p hp)).1
  have hF (i : S) (p : ℕ) (hp : p∈P i) (n : ℕ) : F (p*n)=F n := by
    obtain ⟨hprime,hlo,hhi⟩ := giantCandidateFullPrimes_range hx hL (hmem i p hp)
    apply hf p hprime _ _ n
    · exact (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))).trans hlo
    · exact hhi.le.trans (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)))
  have hG (i : S) (p : ℕ) (hp : p∈P i) (n : ℕ) (hn : 0 < n) : G (p*n)=G n := by
    have hU : p∈U := mem_biUnion.mpr ⟨i,mem_univ _,hp⟩
    unfold G giantCandidateAllocationCore
    rw [giantCandidateStrip_mul_prime U (hP i p hp) hU hn]
  exact ⟨giantTwoSidedSharedProduct_invariant hP c F (fun i p hp n _ => hF i p hp n) hn,
    giantTwoSidedSharedProduct_invariant hP c G hG hn,
    giantTwoSidedShared_product_coprime c (fun i p hp => hc p (hmem i p hp))⟩

end
end ArtinMatthews
