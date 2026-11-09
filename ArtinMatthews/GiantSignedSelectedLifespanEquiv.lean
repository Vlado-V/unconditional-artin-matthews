module

public import ArtinMatthews.GiantSignedFixedLifespanEquiv
public import ArtinMatthews.GiantSignedAdmissibleTraceEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! Join the literal selected patterns, fixed-path orders, and actual
admissible birth-distinct traces. -/

namespace ArtinMatthews
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}

abbrev GiantSignedSelectedOrderedLifespan
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) (ell : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) :=
  Σ p : ((i : Fin n) → patterns i),
    GiantSignedFixedOrderedLifespan PS PB ell (fun i => C i (p i).val) κ visitQ

variable (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ)
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hq0 : ∀ i, 0 < visitQ i) (hq1 : ∀ i, visitQ i < 1)
    (hb : ∀ g (p : PB g), giantSignedPrimeResidueBaseline p.val visitQ ≠ 0)

def giantSignedSelectedOrderedLifespan_packedEquiv :
    GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ ≃
      GiantSignedPackedAdmissibleChronology PS PB ell patterns C κ :=
  (Equiv.sigmaCongrRight (fun _ : (i : Fin n) → patterns i =>
    giantSignedFixedLifespanEquiv hP hdis hκ hsize hq0 hq1 hb)).trans
    { toFun := fun x => ⟨⟨x.1,x.2.val⟩,x.2.property⟩
      invFun := fun x => ⟨x.val.1,⟨x.val.2,x.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem giantSignedSelectedOrderedLifespan_packedEquiv_val
    (x : GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ) :
    (giantSignedSelectedOrderedLifespan_packedEquiv patterns C κ visitQ hP hdis hκ hsize hq0 hq1 hb x).val =
      ⟨x.1,giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize x.2⟩ :=
  rfl

variable (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (ζ : Fin n → ℝ) (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)

def giantSignedSelectedOrderedLifespan_traceEquiv :
    GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ ≃
      GiantSignedAdmissibleBirthTrace (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K :=
  (giantSignedSelectedOrderedLifespan_packedEquiv patterns C κ visitQ hP hdis hκ hsize hq0 hq1 hb).trans
    (giantSignedAdmissibleBirthTraceEquiv ν V q ρ θ patterns C κ visitQ ζ K).symm

theorem giantSignedSelectedOrderedLifespan_traceEquiv_pack
    (x : GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ) :
    giantSignedAdmissibleBirthTrace_pack ν V q ρ θ patterns C κ visitQ ζ K
      (giantSignedSelectedOrderedLifespan_traceEquiv patterns C κ visitQ hP hdis hκ hsize hq0 hq1 hb
        ν V q ρ θ ζ K x) =
      giantSignedSelectedOrderedLifespan_packedEquiv patterns C κ visitQ hP hdis hκ hsize hq0 hq1 hb x :=
  (giantSignedAdmissibleBirthTraceEquiv ν V q ρ θ patterns C κ visitQ ζ K).apply_symm_apply _

end
end ArtinMatthews
