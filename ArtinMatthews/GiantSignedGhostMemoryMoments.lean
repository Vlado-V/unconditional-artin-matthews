module

public import ArtinMatthews.GiantSignedGhostMemoryUniform


set_option backward.privateInPublic true
@[expose] public section

/-! Exact full-memory exponential moments for the original product
factorial measure. Residue multiplicity is retained in every group. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {B : Type*} [Fintype B] {P : B → Finset ℕ}
  [∀ (g : B) (p : P g), NeZero p.val]

theorem giantSignedMemory_exponential_ennreal_tsum
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (v : ℝ) (hv : 0 ≤ v) :
    (∑' m : GiantSignedMemory P,
      ENNReal.ofReal (giantSignedMemoryMass ν m * v ^ (∑ g, m.1 g))) =
      ∏ g, ENNReal.ofReal (Real.exp ((∑ z : GiantSignedParticle (P g), ν g z.1) * v)) := by
  classical
  have hp (x : GiantSignedMemoryGroups P) :
      ENNReal.ofReal (giantSignedMemoryProductMass ν x * v ^ (∑ g, (x g).1)) =
        ∏ g, ENNReal.ofReal (giantSignedGroupMemoryMass (ν g) (x g) * v ^ (x g).1) := by
    unfold giantSignedMemoryProductMass
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact ENNReal.ofReal_prod_of_nonneg (fun g _ =>
      mul_nonneg (giantSignedGroupMemoryMass_nonneg (ν g) (hν g) (x g)) (pow_nonneg hv _))
  calc
    _ = ∑' x : GiantSignedMemoryGroups P,
        ENNReal.ofReal (giantSignedMemoryProductMass ν x * v ^ (∑ g, (x g).1)) := by
      exact ((giantSignedMemoryGroupEquiv P).symm.tsum_eq
        (fun m : GiantSignedMemory P => ENNReal.ofReal (giantSignedMemoryMass ν m *
          v ^ (∑ g, m.1 g)))).symm
    _ = ∏ g, ∑' t : GiantSignedGroupMemory (P g),
        ENNReal.ofReal (giantSignedGroupMemoryMass (ν g) t * v ^ t.1) := by
      simp_rw [hp]
      exact finiteProduct_tsum_prod (fun g : B => GiantSignedGroupMemory (P g))
        (fun g t => ENNReal.ofReal (giantSignedGroupMemoryMass (ν g) t * v ^ t.1))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro g _
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun t => mul_nonneg (giantSignedGroupMemoryMass_nonneg (ν g) (hν g) t) (pow_nonneg hv _))
        (giantSignedFock_exponential_summable (ν g) (hν g) v hv),
        giantSignedFock_exponential_tsum (ν g) (hν g) v hv]

theorem giantSignedMemory_exponential_summable
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (v : ℝ) (hv : 0 ≤ v) :
    Summable (fun m : GiantSignedMemory P => giantSignedMemoryMass ν m * v ^ (∑ g, m.1 g)) := by
  have hn : (∑' m : GiantSignedMemory P,
      ENNReal.ofReal (giantSignedMemoryMass ν m * v ^ (∑ g, m.1 g))) ≠ ∞ := by
    rw [giantSignedMemory_exponential_ennreal_tsum ν hν v hv]
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  exact (ENNReal.summable_toReal hn).congr (fun m =>
    ENNReal.toReal_ofReal (mul_nonneg (giantSignedMemoryMass_nonneg ν hν m) (pow_nonneg hv _)))

theorem giantSignedMemory_energy_bound
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : GiantSignedMemory P → ℂ) (C u : ℝ)
    (hf : ∀ m, ‖f m‖ ≤ C * u ^ (∑ g, m.1 g)) :
    giantSignedGhostMemoryEnergy ν f ≤ ENNReal.ofReal (C ^ 2) *
      ∏ g, ENNReal.ofReal (Real.exp ((∑ z : GiantSignedParticle (P g), ν g z.1) * u ^ 2)) := by
  rw [← giantSignedMemory_exponential_ennreal_tsum ν hν (u ^ 2) (sq_nonneg _),
    ← ENNReal.tsum_mul_left]
  unfold giantSignedGhostMemoryEnergy
  apply ENNReal.tsum_le_tsum
  intro m
  rw [← ENNReal.ofReal_mul (sq_nonneg C)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ giantSignedMemoryMass ν m * (C * u ^ (∑ g, m.1 g)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hf m) _) (giantSignedMemoryMass_nonneg ν hν m)
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (∑ g, m.1 g) 2, pow_mul]
      ring

theorem giantSignedMemory_energy_ne_top
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : GiantSignedMemory P → ℂ) (C u : ℝ)
    (hf : ∀ m, ‖f m‖ ≤ C * u ^ (∑ g, m.1 g)) :
    giantSignedGhostMemoryEnergy ν f ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (giantSignedMemory_energy_bound ν hν f C u hf)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top))

end
end ArtinMatthews
