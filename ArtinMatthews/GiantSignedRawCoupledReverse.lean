module

public import ArtinMatthews.GiantSignedRawCoupledFibers
public import ArtinMatthews.GiantSignedCoupledReverse
public import ArtinMatthews.GiantSignedSmallEdgeReverse


set_option backward.privateInPublic true
@[expose] public section

/-! Raw reversal keeps the two endpoint bans and the original outer law. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawOuterReverse :
    GiantSignedRawOuterChoice (S := S) PB C ell ≃ GiantSignedRawOuterChoice (S := S) PB C ell where
  toFun i := (i.2.1, i.1, i.2.2)
  invFun i := (i.2.1, i.1, i.2.2)
  left_inv i := by rcases i with ⟨a,b,c⟩; rfl
  right_inv i := by rcases i with ⟨a,b,c⟩; rfl

@[simp]
theorem giantSignedRawOuterReverse_apply
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) :
    giantSignedRawOuterReverse i = (i.2.1, i.1, i.2.2) := rfl

def giantSignedRawCoupledFlip (F : GiantSignedRawCoupledTest PS PB C ell) :
    GiantSignedRawCoupledTest PS PB C ell := fun X Y s t => F Y X t s

theorem giantSignedRawCoupledBlock_reverse_le
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (κ : ℤ) {q ρ : ℝ} (hq : 0 ≤ q) (hρ : 0 ≤ ρ)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (F : GiantSignedRawCoupledTest PS PB C ell) (hF : ∀ X Y s t, 0 ≤ F X Y s t)
    (hs : ∀ X Y x a t m σ, F X Y (x,a,giantSignedMemoryPermute m σ) t = F X Y (x,a,m) t)
    (ht : ∀ X Y s z b m σ, F X Y s (z,b,giantSignedMemoryPermute m σ) = F X Y s (z,b,m))
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (c : GiantSignedPatternCopiedLabels PB C)
    (x z : GiantTwoSidedResidueState PS (k+ell)) :
    giantSignedRawCoupledBlock ν V κ q ρ F i c x z ≤
      ENNReal.ofReal ((giantSignedEdgeReverseConstant vmin vmax (ell+budget)) ^ Fintype.card B) *
        giantSignedRawCoupledBlock ν V (-κ) q ρ (giantSignedRawCoupledFlip F)
          (giantSignedRawOuterReverse i) c z x := by
  let DBig := giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct i.2.2
  let R := (giantSignedEdgeReverseConstant vmin vmax (ell+budget)) ^ Fintype.card B
  let A := giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedPatternCopiedMass ν c
  let D := giantSignedSmallPrefixProduct x * DBig
  let D' := giantSignedSmallPrefixProduct z * DBig
  let G := giantSignedRawCoupledFiberTest F i x z D (giantSignedPatternSourceFill C c)
  let G' := giantSignedRawCoupledFiberTest (giantSignedRawCoupledFlip F)
    (giantSignedRawOuterReverse i) z x D' (giantSignedPatternSourceFill C c)
  have hsmall := giantSignedSmallEdgeWeight_reverse hPS hVS κ DBig hq x z
  change ENNReal.ofReal (A * giantSignedSmallEdgeWeight κ DBig q x z) *
      giantSignedEdgeCoupledENNPairing ν V ρ (κ * (D : ℤ))
        (fun X Y a b old out => ENNReal.ofReal (G X Y a b old out)) ≤
    ENNReal.ofReal R * (ENNReal.ofReal (A * giantSignedSmallEdgeWeight (-κ) DBig q z x) *
      giantSignedEdgeCoupledENNPairing ν V ρ ((-κ) * (D' : ℤ))
        (fun X Y a b old out => ENNReal.ofReal (G' X Y a b old out)))
  rw [← hsmall]
  by_cases hzero : giantSignedSmallEdgeWeight κ DBig q x z = 0
  · simp only [hzero, mul_zero, ENNReal.ofReal_zero, zero_mul, le_refl]
  have hprefix : giantSignedSmallPrefixProduct x = giantSignedSmallPrefixProduct z := by
    have hc : ∀ j : S, ∀ a : Fin k,
        z.val.2 j (Fin.castAdd ell a) = x.val.2 j (Fin.castAdd ell a) := by
      by_contra h
      exact hzero (by rw [giantSignedSmallEdgeWeight_eq hPS hVS κ DBig hq,
        if_neg (fun he => h he.1)])
    unfold giantSignedSmallPrefixProduct
    simp only [hc]
  have hD : D' = D := congrArg (fun p => p * DBig) hprefix.symm
  have hG' : G' = fun X Y a b old out => G Y X b a out old := by
    funext X Y a b old out
    dsimp only [G, G', giantSignedRawCoupledFiberTest, giantSignedRawCoupledFlip,
      giantSignedRawOuterReverse_apply]
    rw [hD]
    simp only [and_comm]
  have hsG : ∀ X Y a b out old σ,
      G X Y a b (giantSignedMemoryPermute old σ) out = G X Y a b old out := by
    intro X Y a b out old σ
    unfold G giantSignedRawCoupledFiberTest
    split_ifs
    · exact hs X Y ((giantTwoSidedResiduePermute i.1.1).symm x)
        ((giantSignedGroupedTuplePermutation i.1.2).symm (giantSignedPatternSourceFill C c a))
        ((giantSignedStatePermute PS i.2.1.1 i.2.1.2).symm
          (z,giantSignedPatternSourceFill C c b,out)) old σ
    · rfl
  have htG : ∀ X Y a b old out σ,
      G X Y a b old (giantSignedMemoryPermute out σ) = G X Y a b old out := by
    intro X Y a b old out σ
    unfold G giantSignedRawCoupledFiberTest
    split_ifs
    · exact ht X Y ((giantSignedStatePermute PS i.1.1 i.1.2).symm
          (x,giantSignedPatternSourceFill C c a,old))
        ((giantTwoSidedResiduePermute i.2.1.1).symm z)
        ((giantSignedGroupedTuplePermutation i.2.1.2).symm (giantSignedPatternSourceFill C c b))
        out σ
    · rfl
  rw [hD, hG', neg_mul]
  have he := giantSignedEdgeCoupledENNPairing_reverse_le ν hν V hvmin hVmin hVmax hρ
    (κ * (D : ℤ)) (ell+budget) (fun j => Nat.add_le_add_left (hC j) ell) G
    (giantSignedRawCoupledFiberTest_nonneg F hF i x z D _) hsG htG
  exact (mul_le_mul_right he _).trans_eq (mul_left_comm _ _ _)

theorem giantSignedRawCoupledPairing_reverse_le
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (κ : ℤ) {q ρ : ℝ} (hq : 0 ≤ q) (hρ : 0 ≤ ρ)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (F : GiantSignedRawCoupledTest PS PB C ell) (hF : ∀ X Y s t, 0 ≤ F X Y s t)
    (hs : ∀ X Y x a t m σ, F X Y (x,a,giantSignedMemoryPermute m σ) t = F X Y (x,a,m) t)
    (ht : ∀ X Y s z b m σ, F X Y s (z,b,giantSignedMemoryPermute m σ) = F X Y s (z,b,m)) :
    giantSignedRawCoupledPairing ν V κ q ρ F ≤
      ENNReal.ofReal ((giantSignedEdgeReverseConstant vmin vmax (ell+budget)) ^ Fintype.card B) *
        giantSignedRawCoupledPairing ν V (-κ) q ρ (giantSignedRawCoupledFlip F) := by
  let I := GiantSignedRawOuterChoice (S := S) PB C ell
  let X := GiantTwoSidedResidueState PS (k+ell)
  let L := GiantSignedPatternCopiedLabels PB C
  let w (i : I) := ENNReal.ofReal (giantSignedRawOuterWeight i)
  let F' := giantSignedRawCoupledFlip F
  let R := ENNReal.ofReal ((giantSignedEdgeReverseConstant vmin vmax (ell+budget)) ^ Fintype.card B)
  let V₁ (i : I) (c : L) (x z : X) := giantSignedRawCoupledBlock ν V κ q ρ F i c x z
  let V₂ (i : I) (c : L) (x z : X) := giantSignedRawCoupledBlock ν V (-κ) q ρ F' i c x z
  let e : I ≃ I := giantSignedRawOuterReverse
  have hV (j : B) : 0 < V j := hvmin.trans_le (hVmin j)
  have hF' (X Y) (s t : GiantSignedState PS PB (k+ell)) : 0 ≤ F' X Y s t := hF Y X t s
  rw [giantSignedRawCoupledPairing_outer hVS hVB ν hν V hV κ q hρ F hF,
    giantSignedRawCoupledPairing_outer hVS hVB ν hν V hV (-κ) q hρ F' hF']
  simp_rw [giantSignedRawCoupledSectionPairing_blocks hVS ν hν V hV _ q hρ F hF,
    giantSignedRawCoupledSectionPairing_blocks hVS ν hν V hV _ q hρ F' hF']
  change (∑ i : I, w i * ∑ c : L, ∑ x : X, ∑ z : X, V₁ i c x z) ≤
    R * ∑ i : I, w i * ∑ c : L, ∑ x : X, ∑ z : X, V₂ i c x z
  have hi (i : I) : (∑ c : L, ∑ x : X, ∑ z : X, V₁ i c x z) ≤
      R * ∑ c : L, ∑ x : X, ∑ z : X, V₂ (e i) c x z := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    calc
      _ ≤ ∑ x : X, ∑ z : X, R * V₂ (e i) c z x := by
        exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ =>
          giantSignedRawCoupledBlock_reverse_le hPS hVS ν hν V hvmin hVmin hVmax
            κ hq hρ budget hC F hF hs ht i c x z
      _ = _ := Finset.sum_comm
  calc
    _ ≤ ∑ i : I, w i * (R * ∑ c : L, ∑ x : X, ∑ z : X, V₂ (e i) c x z) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_right (hi i) _)
    _ = R * ∑ i : I, w (e i) * ∑ c : L, ∑ x : X, ∑ z : X, V₂ (e i) c x z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hw : w (e i) = w i := rfl
      rw [hw, mul_left_comm]
    _ = _ := congrArg (fun a : ℝ≥0∞ => R * a) (e.sum_comp
      (fun i => w i * ∑ c : L, ∑ x : X, ∑ z : X, V₂ i c x z))

end
end ArtinMatthews
