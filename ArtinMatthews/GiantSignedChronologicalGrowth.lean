module

public import ArtinMatthews.GiantSignedRawEdgeGrowth
public import ArtinMatthews.GiantSignedWordDomain


set_option backward.privateInPublic true
@[expose] public section

/-! The unrestricted original word stays in the actual countable visit
domain under the proved full raw row bounds. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

variable (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ BS W : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hW : 0 ≤ W) (budget : ℕ)

include hPS hPB hdis hVS hVB hν hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget in
theorem giantSignedRawEdgeFamilyApply_exponential
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ i ∈ patterns, ∀ g, (C i g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ W)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ s r, ‖η i s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : GiantSignedWordExponential f) :
    GiantSignedWordExponential (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f) := by
  obtain ⟨U, u, hU, hu, h⟩ := hf
  let v := max 1 u
  have hv : 1 ≤ v := le_max_left _ _
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hf' (s : GiantSignedState PS PB (k+ell)) :
      ‖f s‖ ≤ U * v ^ (∑ g, s.2.2.1 g) := (h s).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le (le_max_right _ _) _) hU)
  let R := giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget)
  have hR : 0 ≤ R := giantSignedEdgeUniformConstant_nonneg hρ1 hv0.le
  refine ⟨(patterns.card : ℝ) * W * U * R ^ Fintype.card B * BS ^ Fintype.card S,
    v, by positivity, hv0, ?_⟩
  intro s
  refine (giantSignedRawEdgeFamilyApply_row_bound hPS hPB hdis hVS hVB ν hν V hvmin hV hMass
    hq hq1 hBS hbudget hρ hρ1 hU hv hW budget patterns C hC κ θ ζ K hK η hη f hf' s).trans_eq ?_
  change (patterns.card : ℝ) * W * U * v ^ (∑ g, s.2.2.1 g) *
    R ^ Fintype.card B * BS ^ Fintype.card S = _
  ring

include hPS hPB hdis hVS hVB hν hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget in
theorem giantSignedChronologicalWord_exponential
    (θ : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : GiantSignedWordExponential f) :
    ∀ (n : ℕ) (patterns : Fin n → Finset I)
      (C : Fin n → I → B → Finset (Fin k)),
      (∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget) →
      ∀ (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
        (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell),
        (∀ i v, v ∈ patterns i → ∀ a b aux, ‖K i v a b aux‖ ≤ W) →
      ∀ (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ),
        (∀ i v, v ∈ patterns i → ∀ s r, ‖η i v s r‖ ≤ 1) →
      GiantSignedWordExponential (giantSignedChronologicalWord ν V q ρ θ f n patterns C κ visitQ ζ K η) := by
  intro n
  induction n with
  | zero =>
      intro patterns C hC κ visitQ ζ K hK η hη
      exact giantSignedChronologicalVisit_exponential PS ν hν V (visitQ 0) ρ hf
  | succ n ih =>
      intro patterns C hC κ visitQ ζ K hK η hη
      have ht := ih (fun i => patterns i.succ) (fun i => C i.succ)
        (fun i => hC i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => hK i.succ) (fun i => η i.succ) (fun i => hη i.succ)
      have he := giantSignedRawEdgeFamilyApply_exponential hPS hPB hdis hVS hVB ν hν V
        hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget
        (patterns 0) (C 0) (hC 0) (κ 0) θ (ζ 0) (K 0) (hK 0) (η 0) (hη 0) _ ht
      exact giantSignedChronologicalVisit_exponential PS ν hν V (visitQ 0) ρ he

end
end ArtinMatthews
