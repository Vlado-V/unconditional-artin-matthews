module

public import ArtinMatthews.GiantSignedChronologicalLifespanCoefficient
public import ArtinMatthews.GiantPrimeRowSource


set_option backward.privateInPublic true
@[expose] public section

/-! Counting the actual initial and free slots recovers the original band powers. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem slot_range_card {I Q : Type*} [Fintype I] [Fintype Q]
    (labels : I → Q) (hinj : Function.Injective labels) (r : Q → Prop) [DecidablePred r]
    (hr : ∀ p, r p ↔ ∃ j, labels j = p) :
    (Finset.univ.filter r).card = Fintype.card I := by
  let e : I ↪ Q := ⟨labels, hinj⟩
  have he : Finset.univ.map e = Finset.univ.filter r := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hr p).symm
  rw [← he, Finset.card_map, Finset.card_univ]

private theorem active_run_count_split {n : ℕ} (S : Finset (Fin (n+1))) :
    giantSignedActiveRunCount S =
      (if (0 : Fin (n+1)) ∈ S then 1 else 0) +
        ∑ i : Fin n, if i.succ ∈ S ∧ i.castSucc ∉ S then 1 else 0 := by
  let starts := giantSignedActiveRunStarts S
  have h0 : (0 : Fin (n+1)) ∈ starts ↔ (0 : Fin (n+1)) ∈ S := by
    change (0 : Fin (n+1)) ∈ giantSignedActiveRunStarts S ↔ _
    rw [giantSignedActiveRunStarts, Finset.mem_filter]
    refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
    rintro ⟨j, _, hj⟩
    simp only [Fin.val_zero] at hj
    omega
  have hs (i : Fin n) : i.succ ∈ starts ↔ i.succ ∈ S ∧ i.castSucc ∉ S := by
    change i.succ ∈ giantSignedActiveRunStarts S ↔ _
    rw [giantSignedActiveRunStarts, Finset.mem_filter]
    constructor
    · rintro ⟨hi, hp⟩
      exact ⟨hi, fun h => hp ⟨i.castSucc, h, rfl⟩⟩
    · rintro ⟨hi, hp⟩
      refine ⟨hi, ?_⟩
      rintro ⟨j, hj, he⟩
      have hj' : j = i.castSucc := Fin.ext (by
        simp only [Fin.val_succ, Fin.val_castSucc] at he ⊢
        omega)
      exact hp (hj' ▸ hj)
  calc
    giantSignedActiveRunCount S = ∑ i : Fin (n+1), if i ∈ starts then 1 else 0 := by
      rw [Finset.sum_boole]
      change starts.card = _
      have hfilter : Finset.univ.filter (fun i : Fin (n+1) => i ∈ starts) = starts := by
        ext i
        simp
      rw [hfilter, Nat.cast_id]
    _ = _ := by simp only [Fin.sum_univ_succ, h0, hs]

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B] [DecidableEq S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    {A : (g : B) → PB g → Finset (Fin (n+1))}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (offset : Fin (n+1) → ℤ)

theorem giantSignedChronologicalRunCount_eq (data : GiantSignedChronologicalLifespanCoefficientData c h offset)
    (g : B) :
    (∑ p : PB g, giantSignedActiveRunCount (A g p)) =
      k+ell + ∑ i : Fin n, (ell + (C i g).card) := by
  have h0 : (∑ p : PB g, if (0 : Fin (n+1)) ∈ A g p then 1 else 0) = k+ell := by
    rw [Finset.sum_boole]
    simpa only [Fintype.card_fin, Nat.cast_id] using slot_range_card ((h.state 0).2.1 g) (data.initialInjective g)
      (fun p => (0 : Fin (n+1)) ∈ A g p) (data.initialRange g)
  have hstep (i : Fin n) : (∑ p : PB g, if i.succ ∈ A g p ∧ i.castSucc ∉ A g p then 1 else 0) =
      ell + (C i g).card := by
    rw [Finset.sum_boole]
    simpa only [Fintype.card_fin, Nat.cast_id] using slot_range_card
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g)
      (data.targetInjective i g) (fun p => i.succ ∈ A g p ∧ i.castSucc ∉ A g p)
      (fun p => (data.targetRange i g p).symm)
  simp_rw [active_run_count_split]
  rw [Finset.sum_add_distrib, h0, Finset.sum_comm]
  exact congrArg (fun m : ℕ => k+ell+m) (Finset.sum_congr rfl fun i _ => hstep i)

/-- The literal inverse-band powers from the initial and each free edge list. -/
def giantSignedChronologicalBandNormalization (V : B → ℝ)
    (C : Fin n → B → Finset (Fin k)) (ell : ℕ) : ℂ :=
  ∏ g, (((V g)⁻¹ : ℝ) : ℂ) ^ (k+ell + ∑ i : Fin n, (ell + (C i g).card))

theorem giantSignedChronologicalRunNormalization_eq (V : B → ℝ)
    (data : GiantSignedChronologicalLifespanCoefficientData c h offset) :
    (∏ g, ∏ p : PB g, (((V g)⁻¹ : ℝ) : ℂ) ^ giantSignedActiveRunCount (A g p)) =
      giantSignedChronologicalBandNormalization V C ell := by
  unfold giantSignedChronologicalBandNormalization
  apply Finset.prod_congr rfl
  intro g _
  rw [Finset.prod_pow_eq_pow_sum, giantSignedChronologicalRunCount_eq c h offset data g]

theorem giantSignedChronologicalBandNormalization_eq_original (PB : B → Finset ℕ)
    (C : Fin n → B → Finset (Fin k)) (ell : ℕ) :
    giantSignedChronologicalBandNormalization (fun g => bandReciprocalMass (PB g)) C ell =
      ((markedPhysicalMass (fun g => bandReciprocalMass (PB g)) (k+ell) *
        ∏ i, giantTwoSidedPatternFreshMass PB (C i) ell : ℝ) : ℂ) := by
  have h : (∏ g, (bandReciprocalMass (PB g))⁻¹ ^ (k+ell + ∑ i : Fin n, (ell + (C i g).card))) =
      markedPhysicalMass (fun g => bandReciprocalMass (PB g)) (k+ell) *
        ∏ i, giantTwoSidedPatternFreshMass PB (C i) ell := by
    unfold markedPhysicalMass giantTwoSidedPatternFreshMass
    rw [Finset.prod_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset B)),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g _
    rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
  calc
    _ = Complex.ofRealHom (∏ g, (bandReciprocalMass (PB g))⁻¹ ^
        (k+ell + ∑ i : Fin n, (ell + (C i g).card))) := by
      unfold giantSignedChronologicalBandNormalization
      simp only [map_prod, map_pow]
      rfl
    _ = _ := congrArg Complex.ofRealHom h

theorem giantSignedChronologicalPrimeProduct_eq_source_lifespan (κ : Fin n → ℤ)
    (q : Fin (n+1) → ℝ) (ρ : ℝ) (ha : GiantSignedChronologicalAdmissible κ h)
    (data : GiantSignedChronologicalLifespanCoefficientData c h offset)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0)
    (hV : ∀ g, bandReciprocalMass (PB g) ≠ 0) (hρ : ρ ≠ 0)
    (hb : ∀ g (p : PB g), giantSignedPrimeBaseline q p.val ≠ 0) :
    giantSignedChronologicalPrimeProduct h (fun g p => giantSignedTiltedPrimeLaw (PB g) q p)
      (fun g => bandReciprocalMass (PB g)) κ q ρ =
      giantSignedChronologicalBirthFactor batch *
        giantSignedChronologicalBandNormalization (fun g => bandReciprocalMass (PB g)) C ell *
        ∏ g, ∏ p : PB g,
          ((giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) /
            giantSignedPrimeBaseline q p.val : ℝ) : ℂ) := by
  let V (g : B) := bandReciprocalMass (PB g)
  have hν : (fun g (p : PB g) => giantSignedTiltedPrimeLaw (PB g) q p) =
      (fun g (p : PB g) => giantSignedRowBirthAtom (V g) p.val q) := by
    funext g p
    exact (giantSignedRowBirthAtom_eq_source (PB g) q p).symm
  rw [hν, giantSignedChronologicalPrimeProduct_eq_lifespan c h offset V ρ κ q ha data hw hV hρ hb]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Finset.prod_mul_distrib, giantSignedRowBaseline_eq_source]
  rw [giantSignedChronologicalRunNormalization_eq c h offset V data]
  exact (mul_assoc _ _ _).symm

end
end ArtinMatthews
