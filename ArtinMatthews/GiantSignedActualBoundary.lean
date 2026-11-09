module

public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedBoundaryMass
public import ArtinMatthews.GiantSignedTiltedMass


set_option backward.privateInPublic true
@[expose] public section

/-! The actual tilted empty-memory boundary retains free active labels.
Its mass approaches the original small-state mass with the explicit density error. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStateEnergy_boundary (ν : ∀ g, PB g → ℝ) (M : ℕ) :
    giantSignedStateEnergy PS ν (giantSignedBoundary (M := M)) =
      giantSignedBoundaryEnergy PS ν M := rfl

theorem giantSignedTiltedBoundary_energy {n : ℕ}
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : ∀ j (p : PB j), Pmin ≤ p.val)
    (hsmall : (n : ℝ) / Pmin < 1) (M : ℕ) :
    giantSignedBoundaryEnergy PS (fun j => giantSignedTiltedPrimeLaw (PB j) q) M ≤
      ENNReal.ofReal (((1 - (n : ℝ) / Pmin)⁻¹) ^ (Fintype.card B * M)) := by
  have hν (j : B) (p : PB j) : 0 ≤ giantSignedTiltedPrimeLaw (PB j) q p := by
    rw [giantSignedTiltedPrimeLaw_eq]
    exact mul_nonneg (markedHarmonicAtom_nonneg (PB j) (hVB j))
      (zero_le_one.trans (giantSignedPrimeDensity_band_bounds q hq0 hq1 Pmin hPmin (hp j p) hsmall).1)
  refine (giantSignedBoundaryEnergy_le PS _ hν hP hdis hVS M).trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∏ _j : B, ((1 - (n : ℝ) / Pmin)⁻¹) ^ M := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact pow_nonneg (Finset.sum_nonneg fun p _ => hν j p) _
      · intro j _
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => hν j p)
          (giantSignedTiltedPrimeLaw_sum_bounds (PB j) q (hVB j) hq0 hq1 Pmin hPmin (hp j) hsmall).2 M
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm]

theorem giantSignedTiltedBoundary_energy_error {n : ℕ}
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (Pmin : ℝ) (hPmin : 0 < Pmin) (hp : ∀ j (p : PB j), Pmin ≤ p.val)
    (hsmall : (n : ℝ) / Pmin < 1) (M : ℕ)
    (hActive : ((Fintype.card B * M : ℕ) : ℝ) * ((n : ℝ) / Pmin) ≤ 1 / 2) :
    giantSignedBoundaryEnergy PS (fun j => giantSignedTiltedPrimeLaw (PB j) q) M ≤
      ENNReal.ofReal (1 + 2 * ((Fintype.card B * M : ℕ) : ℝ) * ((n : ℝ) / Pmin)) := by
  refine (giantSignedTiltedBoundary_energy PS hP hdis hVS hVB q hq0 hq1
    Pmin hPmin hp hsmall M).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := giantSignedTilt_inverse_pow_error ((n : ℝ) / Pmin)
    (div_nonneg (Nat.cast_nonneg _) hPmin.le) hsmall (Fintype.card B * M) hActive
  linarith

end
end ArtinMatthews
