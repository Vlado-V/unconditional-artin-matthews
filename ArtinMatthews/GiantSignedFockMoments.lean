module

public import ArtinMatthews.GiantSignedGhostRow
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


set_option backward.privateInPublic true
@[expose] public section

/-! The all-degree factorial measure has finite exponential moments.
The residue multiplicity occurs only in this full Fock mass. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

def giantSignedGroupMemoryMass {P : Finset ℕ} (ν : P → ℝ)
    (m : GiantSignedGroupMemory P) : ℝ :=
  (∏ i, ν (m.2 i).1) / (Nat.factorial m.1 : ℝ)

def GiantSignedGroupSymmetric {P : Finset ℕ} (f : GiantSignedGroupMemory P → ℂ) : Prop :=
  ∀ n, MarkedRawTupleSymmetric n (fun a => f ⟨n, a⟩)

def giantSignedGroupEnergy {P : Finset ℕ} (ν : P → ℝ)
    (f : GiantSignedGroupMemory P → ℂ) : ℝ≥0∞ :=
  ∑' m, ENNReal.ofReal (giantSignedGroupMemoryMass ν m * ‖f m‖ ^ 2)

def giantSignedGroupPairing {P : Finset ℕ} (ν : P → ℝ)
    (f h : GiantSignedGroupMemory P → ℂ) : ℂ :=
  ∑' m, (giantSignedGroupMemoryMass ν m : ℂ) * star (f m) * h m

theorem giantSignedGroupMemoryMass_nonneg {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (m : GiantSignedGroupMemory P) :
    0 ≤ giantSignedGroupMemoryMass ν m :=
  div_nonneg (Finset.prod_nonneg fun i _ => hν (m.2 i).1) (Nat.cast_nonneg _)

theorem giantSignedGroupMemoryMass_pos {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 < ν p) (m : GiantSignedGroupMemory P) :
    0 < giantSignedGroupMemoryMass ν m :=
  div_pos (Finset.prod_pos fun i _ => hν (m.2 i).1) (Nat.cast_pos.mpr (Nat.factorial_pos _))

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

theorem giantSignedFock_particle_mass (ν : P → ℝ) :
    (∑ z : GiantSignedParticle P, ν z.1) = ∑ p : P, (p.val : ℝ) * ν p := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

theorem giantSignedFock_degree_mass (ν : P → ℝ) (v : ℝ) (n : ℕ) :
    (∑ a : Fin n → GiantSignedParticle P,
      giantSignedGroupMemoryMass ν ⟨n, a⟩ * v ^ n) =
      ((∑ z : GiantSignedParticle P, ν z.1) * v) ^ n / (Nat.factorial n : ℝ) := by
  classical
  unfold giantSignedGroupMemoryMass
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, ← Finset.sum_mul]
  rw [← Fintype.sum_pow (fun z : GiantSignedParticle P => ν z.1) n, mul_pow]

theorem giantSignedFock_exponential_hasSum (ν : P → ℝ) (v : ℝ) :
    HasSum (fun n : ℕ => ∑ a : Fin n → GiantSignedParticle P,
      giantSignedGroupMemoryMass ν ⟨n, a⟩ * v ^ n)
      (Real.exp ((∑ z : GiantSignedParticle P, ν z.1) * v)) := by
  simp_rw [giantSignedFock_degree_mass]
  simpa only [Real.exp_eq_exp_ℝ] using
    NormedSpace.expSeries_div_hasSum_exp ((∑ z : GiantSignedParticle P, ν z.1) * v)

theorem giantSignedFock_exponential_summable (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (v : ℝ) (hv : 0 ≤ v) :
    Summable (fun m : GiantSignedGroupMemory P => giantSignedGroupMemoryMass ν m * v ^ m.1) := by
  classical
  apply (summable_sigma_of_nonneg (fun m =>
    mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m) (pow_nonneg hv _))).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype] using (giantSignedFock_exponential_hasSum ν v).summable

theorem giantSignedFock_exponential_tsum (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (v : ℝ) (hv : 0 ≤ v) :
    (∑' m : GiantSignedGroupMemory P, giantSignedGroupMemoryMass ν m * v ^ m.1) =
      Real.exp ((∑ z : GiantSignedParticle P, ν z.1) * v) := by
  rw [(giantSignedFock_exponential_summable ν hν v hv).tsum_sigma']
  · simpa only [tsum_fintype] using (giantSignedFock_exponential_hasSum ν v).tsum_eq
  · intro n
    exact (hasSum_fintype _).summable

theorem giantSignedFock_energy_summable (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ) (_hB : 0 ≤ B) (_hv : 0 ≤ v)
    (hf : ∀ m, ‖f m‖ ≤ B * v ^ m.1) :
    Summable (fun m => giantSignedGroupMemoryMass ν m * ‖f m‖ ^ 2) := by
  apply ((giantSignedFock_exponential_summable ν hν (v ^ 2) (sq_nonneg _)).mul_left
    (B ^ 2)).of_nonneg_of_le
  · intro m
    exact mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m) (sq_nonneg _)
  · intro m
    calc
      _ ≤ giantSignedGroupMemoryMass ν m * (B * v ^ m.1) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hf m) _) (giantSignedGroupMemoryMass_nonneg ν hν m)
      _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm m.1 2, pow_mul]; ring

theorem giantSignedFock_energy_bound (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ) (hB : 0 ≤ B) (hv : 0 ≤ v)
    (hf : ∀ m, ‖f m‖ ≤ B * v ^ m.1) :
    giantSignedGroupEnergy ν f ≤
      ENNReal.ofReal (B ^ 2 * Real.exp ((∑ z : GiantSignedParticle P, ν z.1) * v ^ 2)) := by
  have hs := giantSignedFock_energy_summable ν hν f B v hB hv hf
  unfold giantSignedGroupEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m) (sq_nonneg _)) hs]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑' m : GiantSignedGroupMemory P, B ^ 2 *
        (giantSignedGroupMemoryMass ν m * (v ^ 2) ^ m.1) := by
      apply hs.tsum_le_tsum _
        ((giantSignedFock_exponential_summable ν hν (v ^ 2) (sq_nonneg _)).mul_left (B ^ 2))
      intro m
      calc
        _ ≤ giantSignedGroupMemoryMass ν m * (B * v ^ m.1) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hf m) _) (giantSignedGroupMemoryMass_nonneg ν hν m)
        _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm m.1 2, pow_mul]; ring
    _ = _ := by rw [tsum_mul_left, giantSignedFock_exponential_tsum ν hν _ (sq_nonneg _)]

end
end ArtinMatthews
