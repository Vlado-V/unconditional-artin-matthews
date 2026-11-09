module

public import ArtinMatthews.WeightedMonicConvolution
public import ArtinMatthews.WeightedDegreeMultiples


set_option backward.privateInPublic true
@[expose] public section

/-! The weighted monic Euler/logarithmic-derivative coefficient identity.
All polynomial factorizations, divisor fibers and degree reindexings are
proved explicitly; no character, Gauss sum or Euler identity is assumed. -/
namespace ArtinMatthews.WeightedMonic
noncomputable section
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

theorem primePowerTrace_as_atoms (w : F[X] → ℂ) {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    DavenportHasse.primePowerTrace w k =
      ∑ P ∈ atoms n,if P.natDegree ∣ k then (P.natDegree:ℂ)*w P^(k/P.natDegree) else 0 := by
  have he : DavenportHasse.irreducibleDegreeDivisors (F := F) k =
      (atoms n).filter (fun P => P.natDegree ∣ k) := by
    ext P
    rw [DavenportHasse.mem_irreducibleDegreeDivisors k hk,
      Finset.mem_filter,mem_atoms]
    constructor
    · rintro ⟨hm,hi,hd⟩
      exact ⟨⟨hm,(Nat.le_of_dvd hk hd).trans hkn,hi⟩,hd⟩
    · rintro ⟨⟨hm,_hn,hi⟩,hd⟩
      exact ⟨hm,hi,hd⟩
  rw [DavenportHasse.primePowerTrace,he,Finset.sum_filter]

theorem trace_convolution_eq (w : F[X] → ℂ) (n : ℕ) :
    (∑ P ∈ atoms n, ∑ r ∈ Finset.Icc 1 n,
      if r*P.natDegree ≤ n then (P.natDegree:ℂ)*w P^r*coefficient w (n-r*P.natDegree) else 0) =
      ∑ k ∈ Finset.Icc 1 n,DavenportHasse.primePowerTrace w k * coefficient w (n-k) := by
  calc
    _ = ∑ P ∈ atoms n, ∑ k ∈ Finset.Icc 1 n,
        if P.natDegree ∣ k then (P.natDegree:ℂ)*w P^(k/P.natDegree)*coefficient w (n-k) else 0 := by
      apply Finset.sum_congr rfl
      intro P hP
      exact sum_degree_multiples P.natDegree n ((mem_atoms n P).mp hP).2.2.natDegree_pos
        (fun r k => (P.natDegree:ℂ)*w P^r*coefficient w (n-k))
    _ = ∑ k ∈ Finset.Icc 1 n, ∑ P ∈ atoms n,
        if P.natDegree ∣ k then (P.natDegree:ℂ)*w P^(k/P.natDegree)*coefficient w (n-k) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hk,hkn⟩ := Finset.mem_Icc.mp hk
      rw [primePowerTrace_as_atoms w hk hkn,Finset.sum_mul]
      simp only [ite_mul,zero_mul]

/-- Generic finite weighted Euler recurrence, suitable for applying the
independently established degree coefficient and irreducible trace sums. -/
theorem coefficient_recurrence (w : F[X] → ℂ) (h1 : w 1=1)
    (hm : ∀ P Q,P.Monic → Q.Monic → w (P*Q)=w P*w Q) (n : ℕ) :
    (n:ℂ)*coefficient w n =
      ∑ k ∈ Finset.Icc 1 n,DavenportHasse.primePowerTrace w k * coefficient w (n-k) :=
  (coefficient_primePower_convolution w h1 hm n).trans (trace_convolution_eq w n)

end
end ArtinMatthews.WeightedMonic
