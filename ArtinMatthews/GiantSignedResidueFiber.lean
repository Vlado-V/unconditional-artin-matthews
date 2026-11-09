module

public import ArtinMatthews.GiantSignedMemoryCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The actual small-prime torus and pending residue counting fiber. -/
namespace ArtinMatthews
noncomputable section

abbrev GiantSignedResidueFiber {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) :=
  GiantTwoSidedFullResidue PS × GiantSignedResidues primes

def giantSignedResidueDiagonal {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) :
    ℤ →+ GiantSignedResidueFiber PS primes where
  toFun d := (fun _ => (d : ZMod _), fun _ _ => (d : ZMod _))
  map_zero' := by ext <;> simp
  map_add' d e := by ext <;> simp

theorem giantSignedResidueDiagonal_translate {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) (d : ℤ)
    (x : GiantSignedResidueFiber PS primes) :
    x + giantSignedResidueDiagonal PS primes d =
      (giantTwoSidedResidueTranslate d x.1, giantSignedResidueTranslate primes d x.2) := rfl

theorem giantSignedResidueDiagonal_nsmul {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) (d : ℤ) (D : ℕ) :
    D • giantSignedResidueDiagonal PS primes d =
      giantSignedResidueDiagonal PS primes ((D : ℤ) * d) := by
  rw [← map_nsmul]
  congr 1

instance giantSignedResidueFiber_fintype {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val] {degree : B → ℕ}
    (primes : GiantSignedPrimeLists PB degree) : Fintype (GiantSignedResidueFiber PS primes) := by
  classical
  letI : ∀ p : ↥(markedPhysicalBandPrimes PS), Fintype (ZMod p.val) := fun p => by
    let : NeZero p.val := ‹∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val› p
    infer_instance
  change Fintype (GiantTwoSidedFullResidue PS × GiantSignedResidues primes)
  infer_instance

end
end ArtinMatthews
