module

public import ArtinMatthews.GiantRawPhysicalPairing
public import ArtinMatthews.GiantTwoSidedRawSymmetrizedActual


set_option backward.privateInPublic true
@[expose] public section

/-! Position masks put the exact raw rectangular pairing on a common finite slice. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedEndpointInclusion {J : Type*} {P : J → Finset ℕ}
    {M : ℕ} {Z U : Finset ℕ} (hZ : Z ⊆ U) :
    GiantTwoSidedEndpointState P M Z ↪ GiantTwoSidedEndpointState P M U where
  toFun s := ⟨(⟨s.val.1.val, hZ s.val.1.property⟩, s.val.2), s.property⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      exact congrArg (fun v : GiantTwoSidedEndpointState P M U => v.val.1.val) h
    · exact congrArg (fun v : GiantTwoSidedEndpointState P M U => v.val.2) h

theorem giantTwoSidedEndpoint_sum_of_position_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} {Z U : Finset ℕ} (hZ : Z ⊆ U)
    (F : GiantTwoSidedEndpointState P M U → ℂ)
    (hF : ∀ s, s.val.1.val ∉ Z → F s = 0) :
    (∑ s, F s) = ∑ t : GiantTwoSidedEndpointState P M Z,
      F (giantTwoSidedEndpointInclusion hZ t) := by
  classical
  let e := giantTwoSidedEndpointInclusion (P := P) (M := M) hZ
  calc
    _ = ∑ s ∈ Finset.univ.map e, F s := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      apply hF s
      intro hz
      apply hs
      exact Finset.mem_map.mpr
        ⟨⟨(⟨s.val.1.val, hz⟩, s.val.2), s.property⟩, Finset.mem_univ _, rfl⟩
    _ = _ := Finset.sum_map _ _ _

theorem giantTwoSidedRawSlotEntry_inclusion {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m : ℕ} {Z Z' U U' : Finset ℕ}
    (hZ : Z ⊆ U) (hZ' : Z' ⊆ U') (q ζ : ℝ) (χ : DirichletCharacter ℂ m)
    (R : ℕ → ℕ → ℂ) (s : GiantTwoSidedEndpointState P (k+1) Z)
    (t : GiantTwoSidedEndpointState P (k+1) Z') :
    giantTwoSidedRawSlotEntry q ζ χ R (giantTwoSidedEndpointInclusion hZ s)
      (giantTwoSidedEndpointInclusion hZ' t) =
      giantTwoSidedRawSlotEntry q ζ χ R s t := rfl

theorem giantTwoSidedRawPhysical_sum_eq_slicePairing {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k m : ℕ} {Z Z' U : Finset ℕ} (hZ : Z ⊆ U) (hZ' : Z' ⊆ U)
    (x q : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G L : ℕ → ℂ) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k Z Z',
      L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ χ F G e) =
      giantTwoSidedPhysicalWeightedPairing (P := P) (M := k+1) (Z := U)
        (Matrix.of (fun s t => giantTwoSidedRawSlotEntry q 0 χ
          (fun n D => Ψ ((n : ℝ)/(x*(D : ℝ)))/(n : ℂ)) s t))
        (fun s => if s.val.1.val ∈ Z then giantTwoSidedRawPairLeft P k q F L s.val.1.val else 0)
        (fun t => if t.val.1.val ∈ Z' then giantTwoSidedRawPairRight P k q χ G t.val.1.val else 0) := by
  classical
  rw [giantTwoSidedRawPhysical_sum_eq_slots]
  unfold giantTwoSidedPhysicalWeightedPairing
  simp only [markedMatrixPairing_expansion, Matrix.of_apply]
  let State := GiantTwoSidedEndpointState P (k+1) U
  let A (s t : State) := giantTwoSidedRawSlotEntry q 0 χ
    (fun n D => Ψ ((n : ℝ)/(x*(D : ℝ)))/(n : ℂ)) s t
  let f (s : State) := if s.val.1.val ∈ Z then giantTwoSidedRawPairLeft P k q F L s.val.1.val else 0
  let g (t : State) := if t.val.1.val ∈ Z' then giantTwoSidedRawPairRight P k q χ G t.val.1.val else 0
  let σ : ℂ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+1)
  have hleft (s : State) (hs : s.val.1.val ∉ Z) :
      (∑ t : State, A s t * star (f s) * g t) = 0 := by
    simp only [f, ite_eq_right hs, star_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  have hright (s t : State) (ht : t.val.1.val ∉ Z') :
      A s t * star (f s) * g t = 0 := by
    simp only [g, ite_eq_right ht, mul_zero]
  apply congrArg (fun v : ℂ => σ*v)
  symm
  change (∑ s : State, ∑ t : State, A s t * star (f s) * g t) = _
  rw [giantTwoSidedEndpoint_sum_of_position_support hZ _ hleft]
  apply Finset.sum_congr rfl
  intro s _
  rw [giantTwoSidedEndpoint_sum_of_position_support hZ' _ (hright (giantTwoSidedEndpointInclusion hZ s))]
  apply Finset.sum_congr rfl
  intro t _
  have hf : f (giantTwoSidedEndpointInclusion hZ s) =
      giantTwoSidedRawPairLeft P k q F L s.val.1.val := by
    change (if s.val.1.val ∈ Z then giantTwoSidedRawPairLeft P k q F L s.val.1.val else 0) = _
    rw [ite_eq_left s.val.1.property]
  have hg : g (giantTwoSidedEndpointInclusion hZ' t) =
      giantTwoSidedRawPairRight P k q χ G t.val.1.val := by
    change (if t.val.1.val ∈ Z' then giantTwoSidedRawPairRight P k q χ G t.val.1.val else 0) = _
    rw [ite_eq_left t.val.1.property]
  rw [hf, hg]
  unfold A
  rw [giantTwoSidedRawSlotEntry_inclusion]

theorem giantCandidateActualSymmetrizedRawSum_eq_slicePairing {J ι : Type*}
    [Fintype J] [Fintype ι] [DecidableEq ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {m : ℕ} (χ : DirichletCharacter ℂ m)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j k : ℕ) (x : ℝ) :
    let N := ⌊T*x⌋₊
    let Z := giantTwoSidedRawPositionBox P k N
    let Z' := giantTwoSidedRawPositionBox P k (N+1)
    let F := giantCandidateFirstEndpoint e ε x
    let G := giantCandidateAllocationCore C (univ.biUnion P)
      (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
    let Ψ (t : ℝ) : ℂ := ((t*Φ t : ℝ) : ℂ)
    giantCandidateActualSymmetrizedRawSum C P e χ ε Φ T γ q j k x =
      giantTwoSidedPhysicalWeightedPairing (P := P) (M := k+1) (Z := Z ∪ Z')
        (Matrix.of (fun s t => giantTwoSidedRawSlotEntry q 0 χ
          (fun n D => Ψ ((n : ℝ)/(x*(D : ℝ)))/(n : ℂ)) s t))
        (fun s => if s.val.1.val ∈ Z then giantTwoSidedRawPairLeft P k q F (fun _ => 1) s.val.1.val else 0)
        (fun t => if t.val.1.val ∈ Z' then giantTwoSidedRawPairRight P k q χ G t.val.1.val else 0) := by
  intro N Z Z' F G Ψ
  rw [giantCandidateActualSymmetrizedRawSum_eq]
  simpa only [one_mul, giantCandidateActualRawPhysicalSum] using
    giantTwoSidedRawPhysical_sum_eq_slicePairing (P := P) (k := k)
      (U := Z ∪ Z') Finset.subset_union_left Finset.subset_union_right x q Ψ χ F G (fun _ => 1)

end
end ArtinMatthews
