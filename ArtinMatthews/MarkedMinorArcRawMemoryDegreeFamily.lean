module

public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedSubset


set_option backward.privateInPublic true
@[expose] public section

/-! Natural-degree coordinates for the literal total-truncated memory.
These constructors connect the grouped factorial transpose directly to
the actual indexed memory and its measure. -/
namespace ArtinMatthews
open scoped BigOperators

/-- An actual pending memory from its natural degree vector and indexed
particles, with the original total-degree restriction. -/
def markedRawMemoryOfDegrees {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (k : J → ℕ) (hk : (∑ j,k j) ≤ B)
    (a : (j : J) → Fin (k j) → MarkedRawParticle (P j)) : MarkedRawMemory P B :=
  ⟨⟨fun j => ⟨k j,Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun i _ => Nat.zero_le (k i)) (Finset.mem_univ j)).trans hk)⟩,hk⟩,a⟩

/-- Natural-degree construction retains exactly the factorial product
measure of the actual pending memory. -/
theorem markedRawMemoryOfDegrees_mass {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} (k : J → ℕ) (hk : (∑ j,k j) ≤ B)
    (a : (j : J) → Fin (k j) → MarkedRawParticle (P j)) :
    markedRawMemoryMass ν (markedRawMemoryOfDegrees P k hk a)=
      ∏ j,(∏ i,ν j (a j i).1)/(Nat.factorial (k j) : ℝ) := rfl

/-- The same literal measure in the complex scalar convention used by
the signed grouped transpose. -/
theorem markedRawMemoryOfDegrees_mass_complex {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} (k : J → ℕ) (hk : (∑ j,k j) ≤ B)
    (a : (j : J) → Fin (k j) → MarkedRawParticle (P j)) :
    (markedRawMemoryMass ν (markedRawMemoryOfDegrees P k hk a) : ℂ)=
      (∏ j,∏ i,(ν j (a j i).1 : ℂ))/(∏ j,(Nat.factorial (k j) : ℂ)) := by
  rw [markedRawMemoryOfDegrees_mass]
  simp only [Complex.ofReal_prod,Complex.ofReal_div,Complex.ofReal_natCast,Finset.prod_div_distrib]

theorem markedRawMemoryOfDegrees_permute {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (k : J → ℕ) (hk : (∑ j,k j) ≤ B)
    (a : (j : J) → Fin (k j) → MarkedRawParticle (P j))
    (σ : (j : J) → Equiv.Perm (Fin (k j))) :
    markedRawMemoryPermute (markedRawMemoryOfDegrees P k hk a) σ=
      markedRawMemoryOfDegrees P k hk (fun j => a j ∘ σ j) := rfl

/-- Actual pending-index symmetry gives precisely the independent group
symmetry needed in the factorial transpose, including coupled tests. -/
theorem markedRawMemory_symmetric_degree_family {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (f : MarkedRawMemory P B → ℂ)
    (hf : MarkedRawMemorySymmetric f) (k : J → ℕ) (hk : (∑ j,k j) ≤ B) :
    MarkedRawGroupedTupleSymmetric k (fun a => f (markedRawMemoryOfDegrees P k hk a)) := by
  intro a σ
  exact hf (markedRawMemoryOfDegrees P k hk a) σ

/-- Every actual raw memory is recovered without quotienting its indexed
particle lists or changing the total-degree cutoff. -/
theorem markedRawMemoryOfDegrees_recover {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) :
    markedRawMemoryOfDegrees P (fun j => (m.1.1 j : ℕ)) m.1.2 m.2=m := by
  rcases m with ⟨⟨k,hk⟩,a⟩
  rfl

/-- Equality of the literal degree vector and every transported old
coordinate identifies an actual memory with its natural-degree form. -/
theorem markedRawMemory_eq_of_degrees {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (k : J → ℕ) (hcap : (∑ j,k j) ≤ B)
    (a : (j : J) → Fin (k j) → MarkedRawParticle (P j))
    (hk : ∀ j,(m.1.1 j : ℕ)=k j)
    (ha : ∀ j i,m.2 j (Fin.cast (hk j).symm i)=a j i) :
    m=markedRawMemoryOfDegrees P k hcap a := by
  rcases m with ⟨sizes,old⟩
  have hs : sizes=(markedRawMemoryOfDegrees P k hcap a).1 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    exact hk j
  cases hs
  have hOld : old=a := by
    funext j i
    have hi : Fin.cast (hk j).symm i=i := Fin.ext rfl
    simpa only [hi] using ha j i
  cases hOld
  rfl

end ArtinMatthews
