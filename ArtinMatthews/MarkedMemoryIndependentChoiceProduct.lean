module

public import ArtinMatthews.MarkedMemoryIndependentChoiceScalar
public import ArtinMatthews.MarkedMemoryIndependentPathChoices
public import ArtinMatthews.MarkedMemoryPathEndpointData


set_option backward.privateInPublic true
@[expose] public section

/-! Exact primewise coefficient product on the original bands. Primes
outside the actual identity image contribute one; injective numeric
identity labels give the genuine finite product reindex. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))

local notation "path" => markedMemoryIndependentActivePath hZ d hinj
local notation "choices" => markedMemoryIndependentPathChoices hZ d
local notation "emb" => markedMemoryIndependentBandPrimeEmbedding hZ d hinj

def markedMemoryIndependentPrimeChoiceFactor (q : ℝ) (atom : (j : J) → ↥(P j) → ℝ)
    (j : J) (p : P j) : ℝ :=
  markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n) (markedMemoryPathPrimeLines hZ path p)
    (markedMemoryPathVisits path j p) (atom j p) (choices j p)

def markedMemoryIndependentPrimeChoiceProduct (q : ℝ) (atom : (j : J) → ↥(P j) → ℝ) : ℝ :=
  ∏ j,∏ p : P j,markedMemoryIndependentPrimeChoiceFactor hZ d hinj q atom j p

theorem markedMemoryIndependentPrimeChoiceFactor_absent (q : ℝ) (atom : (j : J) → ↥(P j) → ℝ)
    (j : J) (p : P j) (hp : ¬∃ a : A j,(d.particle j a).1=p) :
    markedMemoryIndependentPrimeChoiceFactor hZ d hinj q atom j p=1 := by
  unfold markedMemoryIndependentPrimeChoiceFactor
  rw [markedMemoryIndependentPathVisits_absent hZ d hinj j p hp]
  simp [markedMemoryIndependentPathChoices,hp,markedMemoryPrimeLifespanChoiceWeight,markedMemoryOrphanChoice]

variable (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))

include hempty hterminal hn order ha in
theorem markedMemoryIndependentPrimeChoiceFactor_at (q : ℝ) (atom : (j : J) → ↥(P j) → ℝ)
    (j : J) (a : A j) :
    markedMemoryIndependentPrimeChoiceFactor hZ d hinj q atom j (d.particle j a).1=
      atom j (d.particle j a).1*markedMemoryIndependentEndpointScalar hZ d q ⟨j,a⟩ := by
  unfold markedMemoryIndependentPrimeChoiceFactor
  rw [markedMemoryIndependentPathVisits_at hZ d hinj j a,
    markedMemoryIndependentPathChoices_at hZ d hinj j a]
  exact markedMemoryIndependentChoiceWeight_scalar hZ d hempty hterminal hn order ha q _ j a

include hempty hterminal hn order ha in
theorem markedMemoryIndependentPrimeChoiceProduct_eq (q : ℝ) (atom : (j : J) → ↥(P j) → ℝ) :
    markedMemoryIndependentPrimeChoiceProduct hZ d hinj q atom=
      ∏ a : Σ j,A j,atom a.1 (d.particle a.1 a.2).1*markedMemoryIndependentEndpointScalar hZ d q a := by
  unfold markedMemoryIndependentPrimeChoiceProduct
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  let S : Finset (P j) := Finset.univ.image (emb j)
  have hs : S⊆Finset.univ := Finset.subset_univ _
  calc
    _ = ∏ p∈S,markedMemoryIndependentPrimeChoiceFactor hZ d hinj q atom j p := by
      symm
      apply Finset.prod_subset hs
      intro p _ hp
      apply markedMemoryIndependentPrimeChoiceFactor_absent hZ d hinj q atom j p
      rintro ⟨a,he⟩
      apply hp
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,he⟩
    _ = ∏ a : A j,markedMemoryIndependentPrimeChoiceFactor hZ d hinj q atom j (emb j a) := by
      rw [Finset.prod_image (fun a _ b _ h => (emb j).injective h)]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      exact markedMemoryIndependentPrimeChoiceFactor_at hZ d hinj hempty hterminal hn order ha q atom j a

end
end ArtinMatthews
