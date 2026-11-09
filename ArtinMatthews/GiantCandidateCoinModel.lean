module

public import ArtinMatthews.GiantCandidateActualGroupTests
public import ArtinMatthews.GiantCandidateCoinHits
public import ArtinMatthews.GiantCandidateModelRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The coin probability is the same bounded count test in the actual
box and in the independent residue model. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateCoinModelBands {r : ℕ} (G : Fin r → Finset ℕ) : Fin r × Bool → Finset ℕ :=
  fun i => G i.1

def giantCandidateCoinModelSides (r : ℕ) : Fin r × Bool → GiantCandidateHitSide :=
  fun i => giantCandidateHitSideOfBool i.2

def giantCandidateCoinCountTest {r : ℕ} (G : Fin r → Finset ℕ) (c q : ℝ)
    (j : ℕ) (i : Fin r) (k : Fin r × Bool → ℕ) : ℝ :=
  giantCandidateCoinTest c q j (bandReciprocalMass (G i)) (k (i,true)) (k (i,false))

def giantCandidateCoinModelValue {r : ℕ} (G : Fin r → Finset ℕ) (c q : ℝ)
    (j : ℕ) (i : Fin r) (t : GiantCandidateModelResidueSpace (giantCandidateCoinModelBands G) j) : ℝ :=
  giantCandidateCoinCountTest G c q j i
    (giantCandidateModelHitCounts (giantCandidateCoinModelBands G) (giantCandidateCoinModelSides r) t)

theorem giantCandidateCoinCountTest_actual {r j : ℕ} (x c q : ℝ)
    (g : Fin r → GiantCandidateGroupIndex x) (i : Fin r) (t : Fin j → ℕ) :
    giantCandidateCoinCountTest (fun a => giantCandidateGroup x (g a)) c q j i
      (giantCandidateActualHitCounts
        (giantCandidateCoinModelBands (fun a => giantCandidateGroup x (g a)))
        (giantCandidateCoinModelSides r) t) =
      giantCandidateCoinSuccess x c q j (∏ v,t v) (g i) := by
  rfl

theorem giantCandidateCoinCountTest_unitInterval {r j : ℕ} (G : Fin r → Finset ℕ)
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) (hj : 0<j) (i : Fin r)
    (hV : Real.log 2/2≤bandReciprocalMass (G i)) (k : Fin r × Bool → ℕ) :
    giantCandidateCoinCountTest G (giantCandidateCoinScale q j) q j i k∈Set.Icc (0:ℝ) 1 := by
  obtain ⟨hc,_,hs⟩ := giantCandidateCoinScale_bounds hq₀ hq₁ j hj
  exact giantCandidateCoinTest_mem_unitInterval hc.le hq₀ hq₁ j hj hV hs.le _ _

theorem giantCandidateCoinModelValue_restrict {r s : ℕ}
    (G : Fin r → Finset ℕ) (D : Fin s → Finset ℕ)
    (h : giantCandidateSelectionPrimes (giantCandidateCoinModelBands D) ⊆
      giantCandidateSelectionPrimes (giantCandidateCoinModelBands G))
    (c q : ℝ) (j : ℕ) (i : Fin r) (l : Fin s) (he : G i=D l)
    (t : GiantCandidateModelResidueSpace (giantCandidateCoinModelBands G) j) :
    giantCandidateCoinModelValue G c q j i t =
      giantCandidateCoinModelValue D c q j l
        (giantCandidateModelRestrict (giantCandidateCoinModelBands G) (giantCandidateCoinModelBands D) h t) := by
  have ha := giantCandidateModelHitCounts_restrict (giantCandidateCoinModelBands G)
    (giantCandidateCoinModelBands D) h (giantCandidateCoinModelSides r) (giantCandidateCoinModelSides s)
    (i,true) (l,true) he rfl t
  have hb := giantCandidateModelHitCounts_restrict (giantCandidateCoinModelBands G)
    (giantCandidateCoinModelBands D) h (giantCandidateCoinModelSides r) (giantCandidateCoinModelSides s)
    (i,false) (l,false) he rfl t
  unfold giantCandidateCoinModelValue giantCandidateCoinCountTest
  rw [ha,hb,he]

def giantCandidateSingleModelCoinMean (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (c q : ℝ) (j : ℕ) : ℝ :=
  𝔼 t∈giantCandidateModelResidueTuples
    (giantCandidateCoinModelBands (fun _ : Fin 1 => P)) (fun _ => hP) j,
    giantCandidateCoinModelValue (fun _ : Fin 1 => P) c q j 0 t

theorem giantCandidateSingleModelCoinMean_unitInterval (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) (j : ℕ) (hj : 0<j)
    (hV : Real.log 2/2≤bandReciprocalMass P) :
    giantCandidateSingleModelCoinMean P hP (giantCandidateCoinScale q j) q j∈Set.Icc (0:ℝ) 1 := by
  let G : Fin 1 → Finset ℕ := fun _ => P
  let T := giantCandidateModelResidueTuples (giantCandidateCoinModelBands G) (fun _ => hP) j
  let f := giantCandidateCoinModelValue G (giantCandidateCoinScale q j) q j 0
  have hf (t : GiantCandidateModelResidueSpace (giantCandidateCoinModelBands G) j) :
      f t∈Set.Icc (0:ℝ) 1 := giantCandidateCoinCountTest_unitInterval G hq₀ hq₁ hj 0 hV _
  change 0≤(𝔼 t∈T,f t) ∧ (𝔼 t∈T,f t)≤1
  constructor
  · exact expect_nonneg (fun t _ => (hf t).1)
  · have hT : T.Nonempty := giantCandidateModelResidueTuples_nonempty
      (giantCandidateCoinModelBands G) (fun _ => hP) j
    exact (expect_le_expect (fun t _ => (hf t).2)).trans_eq (expect_const hT 1)

end
end ArtinMatthews
