module

public import ArtinMatthews.MarkedMinorArcDirtyOmission
public import ArtinMatthews.MarkedMinorArcDirtySeparation
public import ArtinMatthews.MarkedMinorArcDirtyPending


set_option backward.privateInPublic true
@[expose] public section

/-! Actual numeric dirty choices: literal copied products, the source ban,
and the source anchor interval. Their charged omission mass is derived. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyNumericChoices {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (source : J → Fin M → ℕ) (Zs : Finset ℕ) (Q : Finset ℤ) (T : ℤ)
    (r A : AddCircle (1:ℝ)) (p : ℕ) : Finset ((J → Fin M) × ℕ) := by
  classical
  exact (Finset.univ.product Zs).filter (fun c =>
    (∀ j k, ¬source j k ∣ c.2) ∧
      ((markedSourceCopiedProduct source c.1*c.2:ℕ):ℤ) ∈ markedMinorDirtyAnchorTrials Q T r A p)

/-- Actual source factors and the ban separate the unique surviving DZ into
its omission tuple and its other-promoted numeric product. -/
theorem markedDirtyNumericChoices_card_le_one {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin M → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) (Zs : Finset ℕ) (Q : Finset ℤ) (T : ℤ)
    (r A : AddCircle (1:ℝ)) {p : ℕ} {ε : ℝ} (hε : 0 < ε) (hp : 1/(p:ℝ) ≤ ε)
    (hg : r ∉ markedPairBadRoots Q T (100*ε)) :
    (markedDirtyNumericChoices source Zs Q T r A p).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro c hc d hd
  have hc' := (Finset.mem_filter.mp hc).2
  have hd' := (Finset.mem_filter.mp hd).2
  have he : ((markedSourceCopiedProduct source c.1*c.2:ℕ):ℤ)=
      ((markedSourceCopiedProduct source d.1*d.2:ℕ):ℤ) :=
    (Finset.card_le_one.mp (markedMinorDirtyAnchorTrials_card_le_one Q T r A hε hp hg)) _ hc'.2 _ hd'.2
  have hP : 0 < markedSourceFullProduct source :=
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (hprime j _ (hsource j k)).pos))
  have hsep := marked_source_ban_product_separation hP
    (markedSourceCopied_dvd_full source c.1) (markedSourceCopied_dvd_full source d.1)
    (markedSourceFull_coprime_of_ban source (fun j k => hprime j _ (hsource j k)) hc'.1)
    (markedSourceFull_coprime_of_ban source (fun j k => hprime j _ (hsource j k)) hd'.1)
    (by exact_mod_cast he)
  exact Prod.ext (markedSourceCopiedProduct_injective P hprime hdis source hsource hdist hsep.1) hsep.2

theorem markedDirtyNumericChoices_omission_mass_le {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin M → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) (Zs : Finset ℕ) (Q : Finset ℤ) (T : ℤ)
    (r A : AddCircle (1:ℝ)) {p : ℕ} {ε : ℝ} (hε : 0 < ε) (hp : 1/(p:ℝ) ≤ ε)
    (hg : r ∉ markedPairBadRoots Q T (100*ε)) :
    (∑ c ∈ markedDirtyNumericChoices source Zs Q T r A p,
      markedUniformOmissionWeight M c.1) ≤ (M:ℝ)⁻¹^(Fintype.card J) := by
  have hc := markedDirtyNumericChoices_card_le_one P hprime hdis source hsource hdist Zs Q T r A hε hp hg
  simp only [markedUniformOmissionWeight_eq,Finset.sum_const,nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)).trans_eq (one_mul _)

/-- Fixing one distinguished old index costs its actual group length ≤B,
while the compatible numeric omission choice retains its true M^(-K) mass. -/
theorem markedDirty_charged_omission_mass_le {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin M → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j))
    {Praw : J → Finset Nat.Primes} {B : ℕ} (memory : MarkedRawMemory Praw B) (jstar : J)
    (Zs : Finset ℕ) (Q : Finset ℤ) (T : ℤ) (r : AddCircle (1:ℝ))
    (anchor : Fin (memory.1.1 jstar:ℕ) → AddCircle (1:ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hp : ∀ k, 1/((memory.2 jstar k).1.1:ℕ) ≤ ε)
    (hg : r ∉ markedPairBadRoots Q T (100*ε)) :
    (∑ k : Fin (memory.1.1 jstar:ℕ),
      ∑ c ∈ markedDirtyNumericChoices source Zs Q T r (anchor k) ((memory.2 jstar k).1.1:ℕ),
        markedUniformOmissionWeight M c.1) ≤ (B:ℝ)*(M:ℝ)⁻¹^(Fintype.card J) := by
  calc
    _ ≤ ∑ _k : Fin (memory.1.1 jstar:ℕ), (M:ℝ)⁻¹^(Fintype.card J) :=
      Finset.sum_le_sum (fun k _ => markedDirtyNumericChoices_omission_mass_le P hprime hdis source
        hsource hdist Zs Q T r (anchor k) hε (hp k) hg)
    _ = ((memory.1.1 jstar:ℕ):ℝ)*(M:ℝ)⁻¹^(Fintype.card J) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast markedRawMemory_group_size_le memory jstar)
      (by positivity)

end ArtinMatthews
