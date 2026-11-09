module

public import ArtinMatthews.DavenportHasseMonicFrames


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite sets of bounded-degree monic irreducible polynomials.
These are obtained from coefficient vectors, not from a finiteness premise. -/
namespace ArtinMatthews.DavenportHasse
open Polynomial
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem exists_monicFrame_iff (n : ℕ) (P : F[X]) :
    (∃ a : Fin n → F, monicFrame n a=P) ↔ P.Monic ∧ P.natDegree=n := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨monicFrame_monic n a,monicFrame_natDegree n a⟩
  · rintro ⟨hm,hd⟩
    let Q : MonicDegreeEq F n := MonicDegreeEq.mk P hm hd
    refine ⟨monicCoefficientEquiv n Q,?_⟩
    have h := congrArg Subtype.val ((monicCoefficientEquiv n).symm_apply_apply Q)
    exact h

def monicPolynomialsThrough (n : ℕ) : Finset F[X] :=
  (Finset.range (n+1)).biUnion (fun d => Finset.univ.image (monicFrame (F := F) d))

theorem mem_monicPolynomialsThrough (n : ℕ) (P : F[X]) :
    P ∈ monicPolynomialsThrough n ↔ P.Monic ∧ P.natDegree ≤ n := by
  simp only [monicPolynomialsThrough,Finset.mem_biUnion,Finset.mem_range,Finset.mem_image,Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨d,hd,a,ha⟩
    obtain ⟨hm,hdeg⟩ := (exists_monicFrame_iff d P).mp ⟨a,ha⟩
    exact ⟨hm,hdeg.trans_le (Nat.le_of_lt_succ hd)⟩
  · rintro ⟨hm,hd⟩
    obtain ⟨a,ha⟩ := (exists_monicFrame_iff P.natDegree P).mpr ⟨hm,rfl⟩
    exact ⟨P.natDegree,Nat.lt_succ_of_le hd,a,ha⟩

omit [Fintype F] in
theorem monicFrame_injective (n : ℕ) : Function.Injective (monicFrame (F := F) n) := by
  intro a b h
  funext i
  exact (monicFrame_coeff_lt n a i i.2).symm.trans
    ((congrArg (fun P : F[X] => P.coeff i) h).trans (monicFrame_coeff_lt n b i i.2))

theorem monic_degree_layer_eq_image (n : ℕ) :
    (monicPolynomialsThrough (F := F) n).filter (fun P => P.natDegree=n) =
      Finset.univ.image (monicFrame (F := F) n) := by
  ext P
  simp only [Finset.mem_filter,mem_monicPolynomialsThrough,Finset.mem_image,Finset.mem_univ,true_and]
  rw [exists_monicFrame_iff]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,h.2.le⟩,h.2⟩

theorem monic_degree_sum_eq (w : F[X] → ℂ) (n : ℕ) :
    (∑' P : MonicDegreeEq F n, w P.1) =
      ∑ P ∈ (monicPolynomialsThrough n).filter (fun P => P.natDegree=n), w P := by
  have h := (monicCoefficientEquiv (F := F) n).symm.tsum_eq (fun P : MonicDegreeEq F n => w P.1)
  rw [monic_degree_layer_eq_image,Finset.sum_image]
  · simpa only [tsum_fintype,monicCoefficientEquiv_symm] using h.symm
  · exact fun a _ b _ hab => monicFrame_injective n hab

def irreducibleDegreeDivisors (n : ℕ) : Finset F[X] :=
  (monicPolynomialsThrough n).filter (fun P => Irreducible P ∧ P.natDegree ∣ n)

theorem mem_irreducibleDegreeDivisors (n : ℕ) (hn : 0 < n) (P : F[X]) :
    P ∈ irreducibleDegreeDivisors n ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ∣ n := by
  rw [irreducibleDegreeDivisors,Finset.mem_filter,mem_monicPolynomialsThrough]
  constructor
  · exact fun h => ⟨h.1.1,h.2.1,h.2.2⟩
  · rintro ⟨hm,hi,hd⟩
    exact ⟨⟨hm,Nat.le_of_dvd hn hd⟩,hi,hd⟩

def primePowerTrace (w : F[X] → ℂ) (n : ℕ) : ℂ :=
  ∑ P ∈ irreducibleDegreeDivisors (F := F) n, (P.natDegree : ℂ)*w P^(n/P.natDegree)

end
end ArtinMatthews.DavenportHasse
