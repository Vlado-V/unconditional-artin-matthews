module

public import ArtinMatthews.GiantSignedLifespanEdgeTarget
public import ArtinMatthews.GiantSignedEdgeMoveExpansion
public import ArtinMatthews.GiantSignedPrimeChronologicalStatusWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The literal edge coefficients reindexed by the primes of each band. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem prime_index_product {ι P : Type*} [Fintype P]
    (s : Finset ι) (label : ι → P) (hinj : Function.Injective label)
    (r : P → Prop) [DecidablePred r] (hr : ∀ p, r p ↔ ∃ j ∈ s, label j = p) (f : P → ℂ) :
    (∏ j ∈ s, f (label j)) = ∏ p : P, if r p then f p else 1 := by
  let e : ι ↪ P := ⟨label, hinj⟩
  have hs : s.map e = Finset.univ.filter r := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hr p).symm
  rw [← Finset.prod_filter, ← hs, Finset.prod_map]
  rfl

private theorem pending_group_product {P : Finset ℕ} (ρ : ℝ)
    (m : GiantSignedGroupMemory P) (pending : Finset P) (anchor : (p : P) → ZMod p.val)
    (h : GiantSignedLifespanMemory pending anchor m) :
    (ρ : ℂ) ^ (Finset.univ.filter (fun j : Fin m.1 => (m.2 j).2 = 0)).card =
      ∏ p : P, if p ∈ pending ∧ anchor p = 0 then (ρ : ℂ) else 1 := by
  let zeros := Finset.univ.filter (fun j : Fin m.1 => (m.2 j).2 = 0)
  have hz (j : Fin m.1) : (m.2 j).2 = 0 ↔ anchor (m.2 j).1 = 0 :=
    Iff.of_eq (congrArg (fun x : GiantSignedParticle P => x.2 = 0) (h.particle_anchor j))
  have hr (p : P) : p ∈ pending ∧ anchor p = 0 ↔ ∃ j ∈ zeros, (m.2 j).1 = p := by
    constructor
    · rintro ⟨hp, hp0⟩
      let j := h.index ⟨p, hp⟩
      have hj : (m.2 j).1 = p := h.index_prime ⟨p, hp⟩
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hz j).mpr ?_⟩, hj⟩
      exact hj.symm ▸ hp0
    · rintro ⟨j, hj, rfl⟩
      exact ⟨h.prime_mem j, (hz j).mp (Finset.mem_filter.mp hj).2⟩
  calc
    _ = ∏ _j ∈ zeros, (ρ : ℂ) := (Finset.prod_const _).symm
    _ = _ := prime_index_product zeros (fun j => (m.2 j).1) h.prime_injective
      (fun p => p ∈ pending ∧ anchor p = 0) hr (fun _ => (ρ : ℂ))

variable {B : Type*} [Fintype B] {P : B → Finset ℕ} {n : ℕ}
    {A : (g : B) → P g → Finset (Fin n)}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))

private theorem pending_memory_product (ρ : ℝ) (m : GiantSignedMemory P)
    (pending : (g : B) → Finset (P g)) (anchor : (g : B) → (p : P g) → ZMod p.val)
    (h : ∀ g, GiantSignedLifespanMemory (pending g) (anchor g) (giantSignedMemoryGroupEquiv P m g)) :
    (giantSignedPendingDamping ρ m : ℂ) =
      ∏ g, ∏ p : P g, if p ∈ pending g ∧ anchor g p = 0 then (ρ : ℂ) else 1 := by
  rw [giantSignedPendingDamping, Complex.ofReal_pow, giantSignedPendingZeros, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun g _ => pending_group_product ρ _ _ _ (h g)

theorem giantSignedLifespanBeforeDamping_eq (ρ : ℝ) (offset : Fin n → ℤ) (i : Fin n)
    (m : GiantSignedMemory P)
    (h : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) i)
      (giantSignedLifespanResidue (c g) offset i) (giantSignedMemoryGroupEquiv P m g)) :
    (giantSignedPendingDamping ρ m : ℂ) = ∏ g, ∏ p : P g, giantSignedPrimeBeforeHalf (c g) ρ offset i p := by
  simpa only [giantSignedPrimeBeforeHalf, mem_giantSignedGhostVisitBefore] using
    pending_memory_product ρ m _ _ h

theorem giantSignedLifespanAfterDamping_eq (ρ : ℝ) (offset : Fin n → ℤ) (i : Fin n)
    (m : GiantSignedMemory P)
    (h : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) i)
      (giantSignedLifespanResidue (c g) offset i) (giantSignedMemoryGroupEquiv P m g)) :
    (giantSignedPendingDamping ρ m : ℂ) = ∏ g, ∏ p : P g, giantSignedPrimeAfterHalf (c g) ρ offset i p := by
  simpa only [giantSignedPrimeAfterHalf, mem_giantSignedGhostVisitAfter] using
    pending_memory_product ρ m _ _ h

theorem giantSignedLifespanInitialMass_eq {M N : ℕ} {active : (g : B) → P g → Finset (Fin (N + 1))}
    (V : B → ℝ) (q : Fin (N + 1) → ℝ) (a : MarkedPhysicalMarking P M)
    (hinj : ∀ g, Function.Injective (a g))
    (hactive : ∀ g (p : P g), (0 : Fin (N + 1)) ∈ active g p ↔ ∃ j, a g j = p) :
    (giantSignedActiveMass (fun g p => giantSignedRowBirthAtom (V g) p.val q) a : ℂ) =
      ∏ g, ∏ p : P g, if (0 : Fin (N + 1)) ∈ active g p then
        (giantSignedRowBirthAtom (V g) p.val q : ℂ) else 1 := by
  change Complex.ofRealHom (∏ g, ∏ j, giantSignedRowBirthAtom (V g) (a g j).val q) = _
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro g _
  exact prime_index_product Finset.univ (a g) (hinj g) _
    (fun p => by simpa only [Finset.mem_univ, true_and] using hactive g p)
    (fun p => (giantSignedRowBirthAtom (V g) p.val q : ℂ))

def giantSignedLifespanEdgePrimeFactor (V ρ : ℝ) (offset : Fin n → ℤ) (q : Fin n → ℝ)
    (v w : Fin n) (g : B) (p : P g) : ℂ :=
  (giantSignedPrimeAfterHalf (c g) ρ offset v p * giantSignedPrimeBeforeHalf (c g) ρ offset w p) *
    ((if giantSignedPrimePromote (c g p) v w then ((V⁻¹ : ℝ) : ℂ) else 1) *
      (if giantSignedPrimeFreshAt (c g p) w then (giantSignedRowBirthAtom V p.val q : ℂ) else 1))

private theorem promotion_slots_range {P₀ : Finset ℕ} {t : ℕ}
    {A₀ : P₀ → Finset (Fin n)} (choice : ∀ p, GiantSignedResidueLifespanChoice (A₀ p))
    (v w : Fin n) (hadj : v.val + 1 = w.val) (target : Fin t → P₀)
    (hrange : ∀ p, (∃ j, target j = p) ↔ w ∈ A₀ p ∧ v ∉ A₀ p) (p : P₀) :
    giantSignedPrimePromote (choice p) v w ↔
      ∃ j ∈ giantSignedLifespanPromoteSlots choice v w target, target j = p := by
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := (hrange p).mpr ((giantSignedPrimeNewActive_adjacent (choice p) v w hadj).mpr (Or.inl hp))
    exact ⟨j, (giantSignedLifespanPromoteSlots_mem choice v w target j).mpr (hj.symm ▸ hp), hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact (giantSignedLifespanPromoteSlots_mem choice v w target j).mp hj

private theorem fresh_slots_range {P₀ : Finset ℕ} {t : ℕ}
    {A₀ : P₀ → Finset (Fin n)} (choice : ∀ p, GiantSignedResidueLifespanChoice (A₀ p))
    (v w : Fin n) (hadj : v.val + 1 = w.val) (target : Fin t → P₀)
    (hrange : ∀ p, (∃ j, target j = p) ↔ w ∈ A₀ p ∧ v ∉ A₀ p) (p : P₀) :
    giantSignedPrimeFreshAt (choice p) w ↔
      ∃ j ∈ (giantSignedLifespanPromoteSlots choice v w target)ᶜ, target j = p := by
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := (hrange p).mpr ((giantSignedPrimeNewActive_adjacent (choice p) v w hadj).mpr (Or.inr hp))
    refine ⟨j, Finset.mem_compl.mpr (fun h => ?_), hj⟩
    have he := (giantSignedLifespanPromoteSlots_mem choice v w target j).mp h
    exact giantSignedPrimePromoteFresh_disjoint (choice p) v w hadj ⟨hj ▸ he, hp⟩
  · rintro ⟨j, hj, rfl⟩
    have ha := (hrange (target j)).mp ⟨j, rfl⟩
    exact ((giantSignedPrimeNewActive_adjacent (choice (target j)) v w hadj).mp ha).resolve_left
      (fun h => (Finset.mem_compl.mp hj) ((giantSignedLifespanPromoteSlots_mem choice v w target j).mpr h))

variable [DecidableEq B] {t : B → ℕ}

theorem giantSignedLifespanEdgeMoveCoefficient_eq (V : B → ℝ) (ρ : ℝ)
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (v w : Fin n) (hadj : v.val + 1 = w.val)
    (d : ℤ) (D : ℕ) (m : GiantSignedMemory P) (source target : GiantSignedPrimeTuple P t)
    (htarget : ∀ g, Function.Injective (target g))
    (hrange : ∀ g p, (∃ j, target g j = p) ↔ w ∈ A g p ∧ v ∉ A g p)
    (hafter : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) v)
      (giantSignedLifespanResidue (c g) offset v) (giantSignedMemoryGroupEquiv P m g))
    (hits : GiantSignedEdgeHits d m target (giantSignedLifespanEdgeChoice c v w offset m hafter source target htarget))
    (ban : GiantSignedEdgePromotionBan D
      (giantSignedLifespanEdgeChoice c v w offset m hafter source target htarget).2.1 target)
    (hbefore : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) w)
      (giantSignedLifespanResidue (c g) offset w) (giantSignedMemoryGroupEquiv P
        (giantSignedEdgeTarget d m source (giantSignedLifespanEdgeChoice c v w offset m hafter source target htarget)) g)) :
    giantSignedEdgeMoveCoefficient (fun g p => (giantSignedRowBirthAtom (V g) p.val q : ℂ)) V ρ d D
      source target m (giantSignedLifespanEdgeChoice c v w offset m hafter source target htarget) =
      ∏ g, ∏ p : P g, giantSignedLifespanEdgePrimeFactor c (V g) ρ offset q v w g p := by
  let T (g : B) := giantSignedLifespanPromoteSlots (c g) v w (target g)
  let ν (g : B) (p : P g) := (giantSignedRowBirthAtom (V g) p.val q : ℂ)
  have hp : giantSignedPromotionCharge V (fun g => (T g).card) =
      ∏ g, ∏ p : P g, if giantSignedPrimePromote (c g p) v w then (((V g)⁻¹ : ℝ) : ℂ) else 1 := by
    unfold giantSignedPromotionCharge
    apply Finset.prod_congr rfl
    intro g _
    rw [← Complex.ofReal_inv]
    exact (Finset.prod_const _).symm.trans (prime_index_product (T g) (target g) (htarget g) _
      (promotion_slots_range (c g) v w hadj (target g) (hrange g))
      (fun _ => (((V g)⁻¹ : ℝ) : ℂ)))
  have hf : giantSignedFreshPrimeMass ν T target =
      ∏ g, ∏ p : P g, if giantSignedPrimeFreshAt (c g p) w then ν g p else 1 := by
    unfold giantSignedFreshPrimeMass
    apply Finset.prod_congr rfl
    intro g _
    rw [show (∏ i, ν g ((markedRawSubsetTupleEquiv (T g) (target g)).2 i)) =
        ∏ j ∈ (T g)ᶜ, ν g (target g j) from
      (((T g)ᶜ.orderIsoOfFin rfl).toEquiv.prod_comp
        (fun j : ↥((T g)ᶜ) => ν g (target g j.val))).trans
        (Finset.prod_coe_sort (s := (T g)ᶜ) (f := fun j => ν g (target g j)))]
    exact prime_index_product (T g)ᶜ (target g) (htarget g) _
      (fresh_slots_range (c g) v w hadj (target g) (hrange g)) _
  unfold giantSignedEdgeMoveCoefficient
  rw [ite_eq_left ⟨hits, ban⟩]
  rw [giantSignedLifespanAfterDamping_eq c ρ offset v m hafter,
    giantSignedLifespanBeforeDamping_eq c ρ offset w _ hbefore]
  change giantSignedPromotionCharge V (fun g => (T g).card) * giantSignedFreshPrimeMass ν T target * _ = _
  rw [hp, hf]
  simp only [giantSignedLifespanEdgePrimeFactor, Finset.prod_mul_distrib, ν]
  ac_rfl

end
end ArtinMatthews
