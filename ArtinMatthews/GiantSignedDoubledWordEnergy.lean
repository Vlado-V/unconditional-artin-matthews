module

public import ArtinMatthews.GiantSignedDoubledChronologicalWord
public import ArtinMatthews.GiantSignedSourceDoubledGrowth
public import ArtinMatthews.GiantSignedChronologicalGrowth
public import ArtinMatthews.GiantSignedRawEdgeSymmetry
public import ArtinMatthews.GiantSignedRawFamilyEnergy
public import ArtinMatthews.GiantSignedSourceAbsoluteCost


set_option backward.privateInPublic true
@[expose] public section

/-! The untruncated doubled word has the actual polynomial energy cost.
Its convergence and pending symmetry follow from the original local rows. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedDoubledChronologicalWord_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax q ρ v BS W C₀ C₁ L : ℝ}
    (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax)
    (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hW : 0 ≤ W)
    (hL : 0 < L) (hS : (Fintype.card S : ℝ) ≤ C₀ * Real.log L)
    (hB : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (budget : ℕ) (θ : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : GiantSignedWordExponential f)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ (n : ℕ) (patterns : Fin n → Finset I)
      (C : Fin n → I → B → Finset (Fin k)),
      (∀ i p, p ∈ patterns i → ∀ g, (C i p g).card ≤ budget) →
      (∀ i, ((patterns i).card : ℝ) * W ≤ L ^ C₁) →
      ∀ (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ),
        (∀ i, 0 ≤ visitQ i ∧ visitQ i ≤ 1) →
        (∀ i, |visitQ i / ρ ^ 2| + |-(1-visitQ i) / ρ| / v ≤ 1) →
        (∀ i g, |visitQ i / ρ ^ 2| + 2 * |-(1-visitQ i) * V g / ρ| / v ≤ 1) →
      ∀ (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell),
        (∀ i p, p ∈ patterns i → ∀ a b aux, ‖K i p a b aux‖ ≤ W) →
      ∀ (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ),
        (∀ i p, p ∈ patterns i → ∀ s r, ‖η i p s r‖ ≤ 1) →
        (∀ i p, p ∈ patterns i → ∀ (s : GiantSignedState PS PB (k+ell))
          (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
          (r : GiantSignedRawEdgeMove PS PB ell (C i p) (giantSignedMemoryPermute s.2.2 σ)),
          η i p (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
            η i p s (giantSignedRawEdgeOldEquiv s.2.2 σ r)) →
      let w := giantSignedDoubledChronologicalWord ν V q ρ θ f n patterns C κ visitQ ζ K η
      GiantSignedWordExponential w ∧
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) ∧
      giantSignedStateEnergy PS ν w ≤
        (ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ (2*vmax) ρ v)) ^ (n+1) *
          (ENNReal.ofReal (L ^ (2 * giantSignedSourceAbsoluteExponent
            C₀ C₁ BS ρ v vmin vmax 2 (ell+budget)))) ^ n * giantSignedStateEnergy PS ν f := by
  let G := ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ (2*vmax) ρ v)
  let A := ENNReal.ofReal (L ^ (2 * giantSignedSourceAbsoluteExponent
    C₀ C₁ BS ρ v vmin vmax 2 (ell+budget)))
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hV0 (g : B) : 0 ≤ V g := hvmin.le.trans (hVmin g)
  intro n
  induction n with
  | zero =>
      intro patterns C hC hcost κ visitQ ζ hqVisit hrow hcol K hK η hη hηeq
      obtain ⟨U, u, hU, hu, hf'⟩ := hf
      refine ⟨giantSignedSourceDoubledVisit_exponential PS ν hν V (visitQ 0) ρ f
        ⟨U,u,hU,hu,hf'⟩,
        giantSignedSourceDoubledVisit_memorySymmetric PS ν hν V (visitQ 0) ρ f
          ⟨U,u,hU,hu,hf'⟩ hsym, ?_⟩
      simpa only [giantSignedDoubledChronologicalWord, Nat.zero_add, pow_zero, pow_one, mul_one]
        using giantSignedSourceDoubledVisit_energy PS ν hν hMass V hvmax hV0 hVmax hVS
          hρ hv0 (hqVisit 0).1 (hqVisit 0).2 hL hB (hrow 0) (hcol 0) f hsym
          U u hU hu (fun s a m => hf' (s,a,m))
  | succ n ih =>
      intro patterns C hC hcost κ visitQ ζ hqVisit hrow hcol K hK η hη hηeq
      let tail := giantSignedDoubledChronologicalWord ν V q ρ θ f n
        (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
      have ht := ih (fun i => patterns i.succ) (fun i => C i.succ)
        (fun i => hC i.succ) (fun i => hcost i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => hqVisit i.succ) (fun i => hrow i.succ) (fun i => hcol i.succ)
        (fun i => K i.succ) (fun i => hK i.succ) (fun i => η i.succ)
        (fun i => hη i.succ) (fun i => hηeq i.succ)
      have htExp : GiantSignedWordExponential tail := ht.1
      have htSym : ∀ s a, GiantSignedMemorySymmetric (fun m => tail (s,a,m)) := ht.2.1
      let w := giantSignedRawEdgeFamilyApply ν V (patterns 0) (C 0) (κ 0)
        q ρ θ (ζ 0) (K 0) (η 0) tail
      have hwExp : GiantSignedWordExponential w := giantSignedRawEdgeFamilyApply_exponential
        hPS hPB hdis hVS hVB ν hν V hvmin hVmin hMass hq hq1 hBS hbudget hρ.le hρ1 hW budget
        (patterns 0) (C 0) (hC 0) (κ 0) θ (ζ 0) (K 0) (hK 0) (η 0) (hη 0) tail htExp
      have hwSym : ∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m)) :=
        giantSignedRawEdgeFamilyApply_symmetric_of_equivariant ν V (patterns 0) (C 0) (κ 0)
          q ρ θ (ζ 0) (K 0) (η 0) (hηeq 0) tail htSym
      have hw : giantSignedStateEnergy PS ν w ≤ A * giantSignedStateEnergy PS ν tail := by
        obtain ⟨U, u, hU, hu, ht'⟩ := htExp
        have htu (s : GiantSignedState PS PB (k+ell)) :
            ‖tail s‖ ≤ U * (max 1 u) ^ (∑ g, s.2.2.1 g) := (ht' s).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le (le_max_right _ _) _) hU)
        have he := giantSignedRawEdgeFamilyApply_energy hPS hPB hdis hVS hVB ν hν V
          hvmin hVmin hVmax hMass hq hq1 hBS hbudget hρ.le hρ1 hv hU (le_max_left _ _) hW
          budget (patterns 0) (C 0) (hC 0) (κ 0) θ (ζ 0) (K 0) (hK 0) (η 0) (hη 0) tail htu htSym
        refine he.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
        exact giantSignedSourceAbsoluteEnergyConstant_le (Fintype.card S) (Fintype.card B)
          (ell+budget) hL (mul_nonneg (Nat.cast_nonneg _) hW) (hcost 0) hBS hS hB
      refine ⟨giantSignedSourceDoubledVisit_exponential PS ν hν V (visitQ 0) ρ w hwExp,
        giantSignedSourceDoubledVisit_memorySymmetric PS ν hν V (visitQ 0) ρ w hwExp hwSym, ?_⟩
      obtain ⟨U, u, hU, hu, hw'⟩ := hwExp
      calc
        _ ≤ G * giantSignedStateEnergy PS ν w := giantSignedSourceDoubledVisit_energy
          PS ν hν hMass V hvmax hV0 hVmax hVS hρ hv0 (hqVisit 0).1 (hqVisit 0).2
          hL hB (hrow 0) (hcol 0) w hwSym U u hU hu (fun s a m => hw' (s,a,m))
        _ ≤ G * (A * giantSignedStateEnergy PS ν tail) := mul_le_mul_right hw G
        _ ≤ G * (A * (G ^ (n+1) * A ^ n * giantSignedStateEnergy PS ν f)) :=
          mul_le_mul_right (mul_le_mul_right ht.2.2 A) G
        _ = _ := by rw [pow_succ G (n+1), pow_succ A n]; ac_rfl

end
end ArtinMatthews
