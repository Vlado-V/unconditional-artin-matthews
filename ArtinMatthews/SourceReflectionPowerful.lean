module

public import ArtinMatthews.SourceFullIdealFactorization
public import Mathlib.Algebra.Squarefree.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The powerful and squarefree coordinates used in the reflected moment.
The square-cube decomposition uses actual normalized ideal factors. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
noncomputable section

variable {ι : Type*}

def sourceReflectionIsPowerful (e : ι →₀ ℕ) : Prop :=
  ∀ P, e P ≠ 1

def sourceReflectionIsSquarefree (e : ι →₀ ℕ) : Prop :=
  ∀ P, e P ≤ 1

def sourceReflectionPowerfulPart (e : ι →₀ ℕ) : ι →₀ ℕ :=
  e.mapRange (fun n => if n = 1 then 0 else n) (by decide)

def sourceReflectionSimplePart (e : ι →₀ ℕ) : ι →₀ ℕ :=
  e.mapRange (fun n => if n = 1 then 1 else 0) (by decide)

theorem sourceReflectionPowerfulPart_powerful (e : ι →₀ ℕ) :
    sourceReflectionIsPowerful (sourceReflectionPowerfulPart e) := by
  intro P
  simp only [sourceReflectionPowerfulPart, Finsupp.mapRange_apply]
  split <;> omega

theorem sourceReflectionSimplePart_squarefree (e : ι →₀ ℕ) :
    sourceReflectionIsSquarefree (sourceReflectionSimplePart e) := by
  intro P
  simp only [sourceReflectionSimplePart, Finsupp.mapRange_apply]
  split <;> omega

theorem sourceReflectionPowerfulSimple_disjoint (e : ι →₀ ℕ) :
    Disjoint (sourceReflectionPowerfulPart e).support (sourceReflectionSimplePart e).support := by
  rw [Finset.disjoint_left]
  intro P hp hd
  simp only [Finsupp.mem_support_iff, sourceReflectionPowerfulPart, sourceReflectionSimplePart,
    Finsupp.mapRange_apply] at hp hd
  split at hp <;> simp_all

theorem sourceReflectionPowerfulSimple_add (e : ι →₀ ℕ) :
    sourceReflectionPowerfulPart e + sourceReflectionSimplePart e = e := by
  ext P
  simp only [sourceReflectionPowerfulPart, sourceReflectionSimplePart, Finsupp.add_apply,
    Finsupp.mapRange_apply]
  split <;> simp_all

theorem sourceReflectionPowerfulSimple_unique {e h d : ι →₀ ℕ}
    (hh : sourceReflectionIsPowerful h) (hd : sourceReflectionIsSquarefree d)
    (hdisj : Disjoint h.support d.support) (he : h + d = e) :
    h = sourceReflectionPowerfulPart e ∧ d = sourceReflectionSimplePart e := by
  have hsum (P : ι) : h P + d P = e P := by
    simpa only [Finsupp.add_apply] using congrArg (fun f : ι →₀ ℕ => f P) he
  have hzero (P : ι) : h P = 0 ∨ d P = 0 := by
    by_cases hp : h P = 0
    · exact Or.inl hp
    · apply Or.inr
      by_contra hdP
      exact Finset.disjoint_left.mp hdisj (Finsupp.mem_support_iff.mpr hp)
        (Finsupp.mem_support_iff.mpr hdP)
  constructor
  · ext P
    simp only [sourceReflectionPowerfulPart, Finsupp.mapRange_apply]
    have := hsum P
    have := hzero P
    have := hh P
    have := hd P
    split <;> omega
  · ext P
    simp only [sourceReflectionSimplePart, Finsupp.mapRange_apply]
    have := hsum P
    have := hzero P
    have := hh P
    have := hd P
    split <;> omega

def sourceReflectionParity (e : ι →₀ ℕ) : ι →₀ ℕ :=
  e.mapRange (fun n => n % 2) (by decide)

def sourceReflectionSquareQuotient (e : ι →₀ ℕ) : ι →₀ ℕ :=
  e.mapRange (fun n => (n - 3 * (n % 2)) / 2) (by decide)

theorem sourceReflectionParity_squarefree (e : ι →₀ ℕ) :
    sourceReflectionIsSquarefree (sourceReflectionParity e) := by
  intro P
  simp only [sourceReflectionParity, Finsupp.mapRange_apply]
  omega

theorem sourceReflectionSquareCube_add {e : ι →₀ ℕ} (h : sourceReflectionIsPowerful e) :
    2 • sourceReflectionSquareQuotient e + 3 • sourceReflectionParity e = e := by
  ext P
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Nat.nsmul_eq_mul,
    sourceReflectionSquareQuotient, sourceReflectionParity, Finsupp.mapRange_apply]
  have := h P
  omega

theorem sourceReflectionSquareCube_unique {e r s : ι →₀ ℕ}
    (hs : sourceReflectionIsSquarefree s) (he : 2 • r + 3 • s = e) :
    r = sourceReflectionSquareQuotient e ∧ s = sourceReflectionParity e := by
  have he' (P : ι) : 2 * r P + 3 * s P = e P := by
    simpa only [Finsupp.add_apply, Finsupp.smul_apply, Nat.nsmul_eq_mul] using
      congrArg (fun f : ι →₀ ℕ => f P) he
  constructor
  · ext P
    simp only [sourceReflectionSquareQuotient, Finsupp.mapRange_apply]
    have := he' P
    have := hs P
    omega
  · ext P
    simp only [sourceReflectionParity, Finsupp.mapRange_apply]
    have := he' P
    have := hs P
    omega

variable (F : Type) [Field F] [NumberField F]

theorem sourceFullExponentIdeal_add (e f : ProbePrime F →₀ ℕ) :
    sourceFullExponentIdeal F (e + f) = sourceFullExponentIdeal F e * sourceFullExponentIdeal F f :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem sourceFullExponentIdeal_nsmul (e : ProbePrime F →₀ ℕ) (n : ℕ) :
    sourceFullExponentIdeal F (n • e) = sourceFullExponentIdeal F e ^ n := by
  induction n with
  | zero => simp [sourceFullExponentIdeal]
  | succ n ih => rw [succ_nsmul, sourceFullExponentIdeal_add, ih, pow_succ]

theorem sourceFullExponentIdeal_squarefree_iff (e : ProbePrime F →₀ ℕ) :
    Squarefree (sourceFullExponentIdeal F e) ↔ sourceReflectionIsSquarefree e := by
  rw [squarefree_iff_nodup_normalizedFactors (sourceFullExponentIdeal_ne_bot F e),
    Multiset.nodup_iff_count_le_one]
  have hc (I : Ideal (𝓞 F)) : (normalizedFactors (sourceFullExponentIdeal F e)).count I =
      (e.embDomain (sourceFullPrimeEmbedding F)) I := by
    rw [← sourceFullExponentIdeal_factorization]
    rfl
  simp only [hc, sourceReflectionIsSquarefree]
  constructor
  · intro h P
    simpa only [Finsupp.embDomain_apply_self] using h (sourceFullPrimeEmbedding F P)
  · intro h I
    by_cases hi : I ∈ Set.range (sourceFullPrimeEmbedding F)
    · obtain ⟨P, rfl⟩ := hi
      simpa only [Finsupp.embDomain_apply_self] using h P
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ hi]
      decide

def sourceReflectionPowerfulIdeal (I : Ideal (𝓞 F)) : Prop :=
  I ≠ ⊥ ∧ sourceReflectionIsPowerful (sourceFullIdealExponents F I)

def sourceReflectionIdealSquare (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  sourceFullExponentIdeal F (sourceReflectionSquareQuotient (sourceFullIdealExponents F I))

def sourceReflectionIdealCube (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  sourceFullExponentIdeal F (sourceReflectionParity (sourceFullIdealExponents F I))

theorem sourceReflectionIdealSquare_ne_bot (I : Ideal (𝓞 F)) :
    sourceReflectionIdealSquare F I ≠ ⊥ :=
  sourceFullExponentIdeal_ne_bot F _

theorem sourceReflectionIdealCube_ne_bot (I : Ideal (𝓞 F)) :
    sourceReflectionIdealCube F I ≠ ⊥ :=
  sourceFullExponentIdeal_ne_bot F _

theorem sourceReflectionIdealCube_squarefree (I : Ideal (𝓞 F)) :
    Squarefree (sourceReflectionIdealCube F I) :=
  (sourceFullExponentIdeal_squarefree_iff F _).2 (sourceReflectionParity_squarefree _)

theorem sourceReflectionIdealSquareCube {I : Ideal (𝓞 F)} (hI : sourceReflectionPowerfulIdeal F I) :
    sourceReflectionIdealSquare F I ^ 2 * sourceReflectionIdealCube F I ^ 3 = I := by
  rw [sourceReflectionIdealSquare, sourceReflectionIdealCube, ← sourceFullExponentIdeal_nsmul,
    ← sourceFullExponentIdeal_nsmul, ← sourceFullExponentIdeal_add,
    sourceReflectionSquareCube_add hI.2, sourceFullIdealExponents_recover F I hI.1]

theorem sourceReflectionIdealSquareCube_unique {I R S : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hS : Squarefree S) (h : R ^ 2 * S ^ 3 = I) :
    R = sourceReflectionIdealSquare F I ∧ S = sourceReflectionIdealCube F I := by
  have hr : R ≠ ⊥ := by
    intro hz
    subst R
    apply hI
    simpa using h.symm
  have hs : S ≠ ⊥ := by
    intro hz
    subst S
    apply hI
    simpa using h.symm
  have hR := sourceFullIdealExponents_recover F R hr
  have hS' := sourceFullIdealExponents_recover F S hs
  have he : 2 • sourceFullIdealExponents F R + 3 • sourceFullIdealExponents F S =
      sourceFullIdealExponents F I := by
    apply sourceFullExponentIdeal_injective F
    rwa [sourceFullExponentIdeal_add, sourceFullExponentIdeal_nsmul, sourceFullExponentIdeal_nsmul,
      hR, hS', sourceFullIdealExponents_recover F I hI]
  have hse : sourceReflectionIsSquarefree (sourceFullIdealExponents F S) :=
    (sourceFullExponentIdeal_squarefree_iff F _).mp (hS'.symm ▸ hS)
  obtain ⟨hrr, hss⟩ := sourceReflectionSquareCube_unique hse he
  constructor
  · rw [← hR, hrr, sourceReflectionIdealSquare]
  · rw [← hS', hss, sourceReflectionIdealCube]

end
end ArtinMatthews.SourceEulerAssembly
