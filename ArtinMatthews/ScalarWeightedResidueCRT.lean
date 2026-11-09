module

public import ArtinMatthews.MarkedProgressionCounting


set_option backward.privateInPublic true
@[expose] public section

/-! Finite weighted residue sums with the literal forced congruence class.
Every endpoint error comes from the sharp interval count. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

def scalarWeightedResidueMass (f : ℕ → ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ a ∈ range p, f p a

def scalarWeightedResidueMean (f : ℕ → ℕ → ℝ) (p : ℕ) : ℝ :=
  scalarWeightedResidueMass f p / p

def scalarWeightedResidueLoss (f : ℕ → ℕ → ℝ) (p n : ℕ) : ℝ :=
  f p (n % p)

def scalarForcedResidueInterval (lo hi Q a : ℕ) : Finset ℕ :=
  (Ioc lo hi).filter (fun n => Nat.ModEq Q n a)

theorem scalarForcedResidueInterval_split (lo hi Q a p r : ℕ)
    (hcop : p.Coprime Q) (hr : r < p) :
    (scalarForcedResidueInterval lo hi Q a).filter (fun n => n % p = r) =
      scalarForcedResidueInterval lo hi (p * Q) (Nat.chineseRemainder hcop r a) := by
  ext n
  have hclass : (Nat.ModEq Q n a ∧ n % p = r) ↔
      Nat.ModEq (p * Q) n (Nat.chineseRemainder hcop r a) := by
    constructor
    · rintro ⟨hQ, hp⟩
      apply Nat.chineseRemainder_modEq_unique hcop _ hQ
      change n % p = r % p
      rwa [Nat.mod_eq_of_lt hr]
    · intro h
      obtain ⟨hp, hQ⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr h
      constructor
      · exact hQ.trans (Nat.chineseRemainder hcop r a).property.2
      · have hpr := hp.trans (Nat.chineseRemainder hcop r a).property.1
        change n % p = r % p at hpr
        rwa [Nat.mod_eq_of_lt hr] at hpr
  simp only [scalarForcedResidueInterval, mem_filter, and_assoc, hclass]

theorem scalarForcedResidueInterval_sum_split (lo hi Q a p : ℕ)
    (hp : 0 < p) (hcop : p.Coprime Q) (f g : ℕ → ℝ) :
    (∑ n ∈ scalarForcedResidueInterval lo hi Q a, f (n % p) * g n) =
      ∑ r ∈ range p, f r *
        ∑ n ∈ scalarForcedResidueInterval lo hi (p * Q) (Nat.chineseRemainder hcop r a), g n := by
  have hpoint (n : ℕ) : f (n % p) * g n =
      ∑ r ∈ range p, if n % p = r then f r * g n else 0 := by
    symm
    rw [sum_eq_single (n % p)]
    · simp
    · intro r _ hr
      simp [Ne.symm hr]
    · intro h
      exact (h (mem_range.mpr (Nat.mod_lt n hp))).elim
  simp_rw [hpoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [← sum_filter, scalarForcedResidueInterval_split lo hi Q a p r hcop (mem_range.mp hr),
    mul_sum]

theorem scalarWeightedResidueMass_nonneg (f : ℕ → ℕ → ℝ) {p : ℕ}
    (hf : ∀ r < p, 0 ≤ f p r) : 0 ≤ scalarWeightedResidueMass f p :=
  sum_nonneg (fun r hr => hf r (mem_range.mp hr))

theorem scalarWeightedResidueMean_nonneg (f : ℕ → ℕ → ℝ) {p : ℕ}
    (hf : ∀ r < p, 0 ≤ f p r) : 0 ≤ scalarWeightedResidueMean f p :=
  div_nonneg (scalarWeightedResidueMass_nonneg f hf) (Nat.cast_nonneg p)

theorem scalarWeightedResidueMean_le_one (f : ℕ → ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) (hf : ∀ r < p, f p r ≤ 1) : scalarWeightedResidueMean f p ≤ 1 := by
  apply (div_le_one (Nat.cast_pos.mpr hp)).mpr
  calc
    scalarWeightedResidueMass f p ≤ ∑ _r ∈ range p, (1 : ℝ) :=
      sum_le_sum (fun r hr => hf r (mem_range.mp hr))
    _ = p := by simp

/-- A weighted intersection of residue conditions has endpoint error bounded by
the product of the actual coefficient masses. -/
theorem scalarWeightedResidue_monomial_error (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hf : ∀ p ∈ P, ∀ r < p, 0 ≤ f p r)
    (lo hi Q a : ℕ) (hlo : lo ≤ hi) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q) :
    |(∑ n ∈ scalarForcedResidueInterval lo hi Q a,
        ∏ p ∈ P, scalarWeightedResidueLoss f p n) -
      (((hi - lo : ℕ) : ℝ) / Q) * ∏ p ∈ P, scalarWeightedResidueMean f p| ≤
      ∏ p ∈ P, scalarWeightedResidueMass f p := by
  classical
  induction P using Finset.induction_on generalizing Q a with
  | empty =>
      simpa [scalarForcedResidueInterval, Nat.cast_sub hlo] using
        marked_interval_residue_error lo hi Q a hlo hQ
  | @insert p P hp ih =>
      have hpP : p.Prime := hP p (mem_insert_self p P)
      have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
      have hf' : ∀ q ∈ P, ∀ r < q, 0 ≤ f q r := fun q hq => hf q (mem_insert_of_mem hq)
      have hpQ : p.Coprime Q := hcop p (mem_insert_self p P)
      have hcop' : ∀ q ∈ P, q.Coprime (p * Q) := by
        intro q hq
        apply Nat.Coprime.mul_right
        · exact (Nat.coprime_primes (hP' q hq) hpP).mpr (fun hqp => hp (hqp ▸ hq))
        · exact hcop q (mem_insert_of_mem hq)
      let H := ((hi - lo : ℕ) : ℝ) / Q
      let B := ∏ q ∈ P, scalarWeightedResidueMean f q
      let E := ∏ q ∈ P, scalarWeightedResidueMass f q
      have hsplit := scalarForcedResidueInterval_sum_split lo hi Q a p hpP.pos hpQ
        (f p) (fun n => ∏ q ∈ P, scalarWeightedResidueLoss f q n)
      simp only [prod_insert hp, scalarWeightedResidueLoss] at hsplit ⊢
      rw [hsplit]
      have hmain : H * (scalarWeightedResidueMean f p * B) =
          ∑ r ∈ range p, f p r * (H / p * B) := by
        rw [← sum_mul]
        dsimp [scalarWeightedResidueMean, scalarWeightedResidueMass]
        ring
      change |(∑ r ∈ range p, f p r *
          ∑ n ∈ scalarForcedResidueInterval lo hi (p * Q) (Nat.chineseRemainder hpQ r a),
            ∏ q ∈ P, f q (n % q)) - H * (scalarWeightedResidueMean f p * B)| ≤
        scalarWeightedResidueMass f p * E
      rw [hmain, ← sum_sub_distrib]
      calc
        _ ≤ ∑ r ∈ range p, |f p r *
            (∑ n ∈ scalarForcedResidueInterval lo hi (p * Q) (Nat.chineseRemainder hpQ r a),
                ∏ q ∈ P, f q (n % q) - H / p * B)| := by
          simp_rw [mul_sub]
          exact abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ range p, f p r * E := by
          apply sum_le_sum
          intro r hr
          rw [abs_mul, abs_of_nonneg (hf p (mem_insert_self p P) r (mem_range.mp hr))]
          apply mul_le_mul_of_nonneg_left _ (hf p (mem_insert_self p P) r (mem_range.mp hr))
          have hh := ih hP' hf' (p * Q) (Nat.chineseRemainder hpQ r a)
            (Nat.mul_pos hpP.pos hQ) hcop'
          have hden : (((hi - lo : ℕ) : ℝ) / (p * Q : ℕ)) = H / p := by
            dsimp [H]
            push_cast
            ring
          simpa only [scalarWeightedResidueLoss, hden] using hh
        _ = _ := by rw [← sum_mul]; rfl

end
end ArtinMatthews
