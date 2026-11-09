module

public import ArtinMatthews.GiantSignedSelectedLifespanEquiv
public import ArtinMatthews.GiantSignedAdmissibleTraceWeight
public import ArtinMatthews.GiantSignedTraceAdmissibleSum


set_option backward.privateInPublic true
@[expose] public section

/-! Reindex the actual unrestricted guarded boundary by its original
fixed paths, supported lifespans, and ordered batches. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs) (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hq0 : ∀ i, 0 < visitQ i) (hq1 : ∀ i, visitQ i < 1)
    (hb : ∀ g (p : PB g), giantSignedPrimeResidueBaseline p.val visitQ ≠ 0)

local notation "One" => fun _ _ _ _ => (1 : ℂ)
local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One
local notation "Traces" => GiantSignedAdmissibleBirthTrace (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K
local notation "Orders" => GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ

include hq0 hq1 hb in
theorem giantSignedGuardedTraceBoundaryPairing_eq_orderedLifespan_sum [Fintype Orders] :
    giantSignedGuardedTraceBoundaryPairing (PS := PS) ν Rows
      (giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K One) =
        ∑ x : Orders, giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ
          (fun i => K i (x.1 i).val)
          (giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize x.2).2 := by
  let e : Orders ≃ Traces := giantSignedSelectedOrderedLifespan_traceEquiv patterns C κ visitQ
    hP hdis hκ hsize hq0 hq1 hb ν V q ρ θ ζ K
  letI : Finite Traces := Finite.of_injective e.symm e.symm.injective
  letI : Fintype Traces := Fintype.ofFinite Traces
  let weight (t : Traces) :=
    ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν t.2.1 : ℝ) : ℂ) *
      giantSignedTraceWeight giantSignedBoundary Rows (t.1,t.2.1,giantSignedEmptyMemory PB) t.2.2.val
  let W (z : GiantSignedPackedChronology PS PB ell patterns C) :=
    giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ (fun i => K i (z.1 i).val) z.2.2
  calc
    _ = ∑ t : Traces, weight t :=
      giantSignedGuardedTraceBoundaryPairing_eq_admissibleBirth_sum ν V q ρ θ patterns C κ visitQ ζ K
    _ = ∑ x : Orders, weight (e x) := (e.sum_comp weight).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      have he := giantSignedSelectedOrderedLifespan_traceEquiv_pack patterns C κ visitQ hP hdis hκ hsize
        hq0 hq1 hb ν V q ρ θ ζ K x
      have hp := giantSignedSelectedOrderedLifespan_packedEquiv_val patterns C κ visitQ
        hP hdis hκ hsize hq0 hq1 hb x
      have hw : weight (e x) = W (giantSignedAdmissibleBirthTrace_pack ν V q ρ θ patterns C κ visitQ ζ K (e x)).val :=
        giantSignedAdmissibleBirthTrace_weight_eq_chronology ν V q ρ θ patterns C κ visitQ ζ K (e x)
      exact hw.trans (congrArg W ((congrArg Subtype.val he).trans hp))

end
end ArtinMatthews
