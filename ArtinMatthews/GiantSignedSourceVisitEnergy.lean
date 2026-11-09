module

public import ArtinMatthews.GiantSignedSourceVisitWeights
public import ArtinMatthews.GiantSignedStateGhostGroup


set_option backward.privateInPublic true
@[expose] public section

/-! The original endpoint and interior visits have one polynomial
energy cost, with a memory weight fixed before the group carriers. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

def giantSignedSourceVisitExponent (C₀ Vmax ρ v : ℝ) : ℝ :=
  C₀ * ((Vmax + 1) / ρ * 2 * v)

theorem giantSignedSourceVisitFactor_le
    {B : Type*} [Fintype B] (P : B → Finset ℕ)
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : P g, ν g p) ≤ 2)
    (V : B → ℝ) {Vmax ρ v C₀ qi L : ℝ}
    (hVmax : 0 ≤ Vmax) (hV0 : ∀ g, 0 ≤ V g) (hV : ∀ g, V g ≤ Vmax)
    (hρ : 0 < ρ) (hv : 0 ≤ v) (hqi0 : 0 ≤ qi) (hqi1 : qi ≤ 1)
    (hL : 0 < L) (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L) :
    (∏ g, ENNReal.ofReal (Real.exp ((|-(1-qi) * V g / ρ| + |-(1-qi) / ρ|) *
      (∑ p : P g, ν g p) * v))) ≤
        ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ Vmax ρ v) := by
  let R := (Vmax + 1) / ρ * 2 * v
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hb (g : B) : |-(1-qi) * V g / ρ| + |-(1-qi) / ρ| ≤ (Vmax+1)/ρ := by
    rw [abs_div, abs_div, abs_mul, abs_neg, abs_of_pos hρ,
      abs_of_nonneg (sub_nonneg.mpr hqi1), abs_of_nonneg (hV0 g)]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hρ.le
    have hm := mul_le_of_le_one_left (hV0 g) (show 1-qi ≤ 1 by linarith)
    nlinarith [hV g]
  have hp (g : B) :
      (|-(1-qi) * V g / ρ| + |-(1-qi) / ρ|) * (∑ p : P g, ν g p) * v ≤ R := by
    dsimp [R]
    apply mul_le_mul_of_nonneg_right _ hv
    exact mul_le_mul (hb g) (hMass g)
      (Finset.sum_nonneg fun p _ => hν g p) (by positivity)
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _), ← Real.exp_sum]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _g : B, R := Finset.sum_le_sum fun g _ => hp g
    _ = (Fintype.card B : ℝ) * R := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (C₀ * Real.log L) * R := mul_le_mul_of_nonneg_right hgroups hR
    _ = _ := by unfold giantSignedSourceVisitExponent R; ring

theorem giantSignedSourceVisitEnergy_exists {q ρ C₀ Vmax : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ ^ 2)
    (hVmax : 0 ≤ Vmax) :
    ∃ v : ℝ, 1 < v ∧
      ∀ (S B : Type*) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
        (PS : S → Finset ℕ) (PB : B → Finset ℕ)
        [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
        [∀ g, ∀ p : PB g, NeZero p.val]
        (M : ℕ) (ν : ∀ g, PB g → ℝ),
        (∀ g p, 0 ≤ ν g p) → (∀ g, (∑ p : PB g, ν g p) ≤ 2) →
      ∀ (V : B → ℝ), (∀ g, 0 ≤ V g) → (∀ g, V g ≤ Vmax) →
        (∀ g, 0 < bandReciprocalMass (PS g)) →
      ∀ (n : ℕ) (i : Fin (n+1)) (L : ℝ),
        0 < L → (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
      ∀ (f : GiantSignedState PS PB M → ℂ),
        (∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) →
      ∀ (Cf u : ℝ), 0 ≤ Cf → 0 < u →
        (∀ s a m, ‖f (s,a,m)‖ ≤ Cf * u ^ (∑ g, m.1 g)) →
        giantSignedStateEnergy PS ν
          (giantSignedStateGhostGroup PS ν V (giantSignedSourceVisitQ q n i) ρ f) ≤
            ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ Vmax ρ v) *
              giantSignedStateEnergy PS ν f := by
  obtain ⟨v, hv, hweights⟩ := giantSignedSourceVisitWeights_exists hq0 hq1 hρ hgap Vmax
  refine ⟨v, hv, ?_⟩
  intro S B _ _ _ _ PS PB _ _ M ν hν hMass V hV0 hV hVS n i L hL hgroups f hsym Cf u hCf hu hf
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  have hrow := (hweights n i 0 le_rfl hVmax).1.le
  have hcol (g : B) :
      |giantSignedSourceVisitQ q n i / ρ ^ 2| +
        |-(1-giantSignedSourceVisitQ q n i) * V g / ρ| / v ≤ 1 := by
    have h := (hweights n i (V g) (hV0 g) (hV g)).2
    have hn : 0 ≤ |-(1-giantSignedSourceVisitQ q n i) * V g / ρ| / v := by positivity
    rw [mul_div_assoc] at h
    nlinarith
  refine (giantSignedStateGhostGroup_energy PS hVS ν hν V _ ρ v hv0 hrow hcol
    f hsym Cf u hCf hu hf).trans ?_
  have hqi0 := (giantSignedSourceVisitQ_bounds hq0 hq1 n i).1
  have hqi1 : giantSignedSourceVisitQ q n i ≤ 1 := by
    have hs := Real.sq_sqrt hq0
    have hn := Real.sqrt_nonneg q
    have hle := (giantSignedSourceVisitQ_bounds hq0 hq1 n i).2
    nlinarith
  exact mul_le_mul_left
    (giantSignedSourceVisitFactor_le PB ν hν hMass V hVmax hV0 hV hρ hv0.le hqi0 hqi1 hL hgroups) _

end
end ArtinMatthews
