module

public import ArtinMatthews.WeightedMonicFactorization
public import ArtinMatthews.DavenportHasseMonicEnumeration


set_option backward.privateInPublic true
@[expose] public section

/-! Point each occurrence in the irreducible factorization by one of its
prime powers. The resulting finite degree identity is the combinatorial
logarithmic derivative, prior to any multiplicative-weight reindexing. -/
namespace ArtinMatthews.WeightedMonic
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

def layer (n : ℕ) : Finset F[X] :=
  (DavenportHasse.monicPolynomialsThrough n).filter (fun P => P.natDegree=n)

def atoms (n : ℕ) : Finset F[X] :=
  (DavenportHasse.monicPolynomialsThrough n).filter Irreducible

def coefficient (w : F[X] → ℂ) (n : ℕ) : ℂ :=
  ∑' P : MonicDegreeEq F n, w P.1

theorem coefficient_sum (w : F[X] → ℂ) (n : ℕ) : coefficient w n = ∑ P ∈ layer n,w P :=
  DavenportHasse.monic_degree_sum_eq w n

theorem mem_layer (n : ℕ) (P : F[X]) : P ∈ layer n ↔ P.Monic ∧ P.natDegree=n := by
  simp only [layer,Finset.mem_filter,DavenportHasse.mem_monicPolynomialsThrough]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,h.2.le⟩,h.2⟩

theorem mem_atoms (n : ℕ) (P : F[X]) : P ∈ atoms n ↔ P.Monic ∧ P.natDegree≤n ∧ Irreducible P := by
  simp only [atoms,Finset.mem_filter,DavenportHasse.mem_monicPolynomialsThrough,and_assoc]

theorem degree_sum_atoms {n : ℕ} {Q : F[X]} (hQ : Q.Monic) (hn : Q.natDegree=n) :
    n = ∑ P ∈ atoms n,exponent P Q * P.natDegree := by
  refine (hn.symm.trans (degree_eq_factor_sum hQ)).trans ?_
  apply Finset.sum_subset
  · intro P hP
    obtain ⟨hi,hm,hd⟩ := factor_spec hQ (Multiset.mem_toFinset.mp hP)
    exact (mem_atoms _ _).mpr ⟨hm,(natDegree_le_of_dvd hd hQ.ne_zero).trans hn.le,hi⟩
  · intro P _ hP
    have hc : exponent P Q = 0 := Multiset.count_eq_zero.mpr (by simpa only [Multiset.mem_toFinset] using hP)
    rw [hc,zero_mul]

theorem sum_initial_segment (C : ℂ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ r ∈ Finset.Icc 1 n,if r≤m then C else 0) = (m:ℂ)*C := by
  rw [←Finset.sum_filter]
  have he : (Finset.Icc 1 n).filter (fun r => r≤m) = Finset.Icc 1 m := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  rw [he,Finset.sum_const,Nat.card_Icc]
  simp

theorem degree_pointed (w : F[X] → ℂ) {n : ℕ} {Q : F[X]} (hQ : Q.Monic) (hn : Q.natDegree=n) :
    (n:ℂ)*w Q = ∑ P ∈ atoms n, ∑ r ∈ Finset.Icc 1 n,
      if P^r ∣ Q then (P.natDegree:ℂ)*w Q else 0 := by
  have hs : (n:ℂ) = ∑ P ∈ atoms n,(exponent P Q:ℂ)*(P.natDegree:ℂ) := by
    exact_mod_cast degree_sum_atoms hQ hn
  rw [hs,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨hm,_hd,hi⟩ := (mem_atoms n P).mp hP
  have he : exponent P Q ≤ n := (exponent_le_degree hm hi hQ).trans hn.le
  have hsum := sum_initial_segment ((P.natDegree:ℂ)*w Q) he
  simp_rw [←power_dvd_iff_exponent hm hi hQ.ne_zero] at hsum
  simpa only [mul_assoc] using hsum.symm

end
end ArtinMatthews.WeightedMonic
