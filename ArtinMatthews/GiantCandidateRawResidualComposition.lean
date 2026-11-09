module

public import ArtinMatthews.GiantRawPhysicalUnmasked
public import ArtinMatthews.GiantTwoSidedPhysicalFamilyCharacter
public import ArtinMatthews.GiantTwoSidedMappedResidualExpansion
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantRawPositionGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The raw term is the empty member of the performed residual family.
The nonempty members remain literal character-twisted comparison cutoffs. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem character_empty_pattern_cutoff {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k M : ℕ} {Z : Finset ℕ}
    (C : J → Finset (Fin k)) (hC : C = giantTwoSidedRawEmptyPattern J k)
    (K : GiantTwoSidedPatternCoefficient P C 1) (hK : ∀ a b aux, K a b aux = 1)
    (χ : DirichletCharacter ℂ M) (q : ℝ) (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+1) Z → ℂ) :
    giantTwoSidedPhysicalPatternCutoffPairing C 1 q 0
        (giantComparisonCharacterCoefficient χ K) Ψ x f g =
      giantTwoSidedPhysicalPatternCutoffPairing (giantTwoSidedRawEmptyPattern J k) 1 q 0
        (giantTwoSidedRawPatternCoefficient χ) Ψ x f g := by
  subst C
  have hcoeff : giantComparisonCharacterCoefficient χ K = giantTwoSidedRawPatternCoefficient χ := by
    funext a b aux
    have haux : giantTwoSidedPatternAuxiliaryProduct aux = 1 := by
      simp [giantTwoSidedPatternAuxiliaryProduct]
    simp only [giantComparisonCharacterCoefficient, giantTwoSidedRawPatternCoefficient,
      hK a b aux, one_mul, giantTwoSidedPatternDilation, haux, mul_one, giantTwoSidedRaw_copiedProduct]
  rw [hcoeff]

/-- A uniform bound on the phased full cutoffs controls the actual raw sum
up to the norms of all literal nonempty comparison cutoffs on the same box. -/
theorem giantCandidateActualRawPhysicalSum_norm_le_mappedResidual_eventually
    {I : Type*} [Fintype I] (e : I → ℝ) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (hΦ : ∀ t, T < t → Φ t = 0)
    (γ q : ℝ) (j k : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let B := GiantCandidatePerformedBig S
      ∀ (probes₁ probes₂ : Finset (B × Fin k)) (Q : ℕ) (h ξ : ℝ),
      let C (p : IdealResidualPattern B k) := giantCandidatePerformedPattern S (idealResidualCopied p)
      let K (p : IdealResidualPattern B k) : GiantTwoSidedPatternCoefficient P (C p) 1 :=
        giantCandidatePerformedCoefficient S
          (idealResidualCoefficient (giantCandidatePerformedBigBand S) Q h ξ p)
      let Z := Ioc 0 ⌊x^2⌋₊
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25 : ℝ))) (x^γ) j
      let Ψ (t : ℝ) : ℂ := ((t*Φ t : ℝ) : ℂ)
      let d (n : ℕ) : ℂ := giantTwoSidedEndpointDamping P (k+1) q n
      let f (n : ℕ) := d n * conj (F n)
      let g (t : GiantTwoSidedEndpointState P (k+1) Z) :=
        d t.val.1.val * (χ t.val.1.val * G t.val.1.val)
      ∀ R : ℝ,
      (∀ r : ZMod M,
        ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
          C 1 q 0 K Ψ x
          (fun n => conj (giantCharacterEndpointPhase r n) * f n)
          (fun t => conj (giantCharacterEndpointPhase r t.val.1.val) * g t)‖ ≤ R) →
      ‖giantCandidateActualRawPhysicalSum (giantCandidateFullPrimes x) P e χ ε Φ T γ q j k x‖ ≤
        (M : ℝ) * R + ∑ A ∈ probes₁.powerset.erase ∅, ∑ B' ∈ probes₂.powerset.erase ∅,
          ‖giantTwoSidedPhysicalPatternCutoffPairing (C (some (A,B'))) 1 q 0
            (giantComparisonCharacterCoefficient χ (K (some (A,B')))) Ψ x f g‖ := by
  filter_upwards [giantCandidateRawPositionBox_cap_eventually k hT,
    giantCandidateSelectedGroups_geometry_eventually, giantCandidateFullPrimes_prime_upper_eventually,
    eventually_gt_atTop (0 : ℝ)] with x hcap hgeom hprime hx
  intro S P B probes₁ probes₂ Q h ξ C K Z F G Ψ d f g R hbound
  have hP (i : S) (p : ℕ) (hp : p ∈ P i) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val, hp⟩)).1
  have hZ : ∀ n ∈ Z, 0 < n := fun _ hn => (mem_Ioc.mp hn).1
  have hleft : giantTwoSidedRawPositionBox P k ⌊T*x⌋₊ ⊆ Z :=
    subset_union_left.trans (hcap S).2
  have hright : giantTwoSidedRawPositionBox P k (⌊T*x⌋₊+1) ⊆ Z :=
    subset_union_right.trans (hcap S).2
  have hC : C none = giantTwoSidedRawEmptyPattern S k := by
    funext i
    rcases i with ⟨i, hi⟩
    cases i <;> rfl
  have hK (a b : MarkedPhysicalMarking P (k+1)) (aux : GiantTwoSidedPatternAuxiliary P (C none)) :
      K none a b aux = 1 := rfl
  let Kχ (p : IdealResidualPattern B k) := giantComparisonCharacterCoefficient χ (K p)
  have hraw := giantCandidateActualRawPhysicalSum_eq_unmasked_patternCutoffPairing
    (P := P) (k := k) (U := Z) e (giantCandidateFullPrimes x) χ ε Φ hx hT.le hΦ γ q j
    hP (hgeom S).1 hZ hleft hright
  have hnone := character_empty_pattern_cutoff (C none) hC (K none) hK χ q Ψ x f g
  have hfull := giantTwoSidedPhysicalCutoffPairing_character_fourier_norm_le
    (idealResidualPatterns probes₁ probes₂) C q 0 χ K Ψ x f g hbound
  calc
    _ = ‖giantTwoSidedPhysicalPatternCutoffPairing (C none) 1 q 0 (Kχ none) Ψ x f g‖ :=
      congrArg norm (hraw.trans hnone.symm)
    _ ≤ ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂) C 1 q 0 Kχ Ψ x f g‖ +
        ∑ A ∈ probes₁.powerset.erase ∅, ∑ B' ∈ probes₂.powerset.erase ∅,
          ‖giantTwoSidedPhysicalPatternCutoffPairing (C (some (A,B'))) 1 q 0
            (Kχ (some (A,B'))) Ψ x f g‖ :=
      giantTwoSidedPhysicalMappedRawCutoffPairing_norm_le probes₁ probes₂ C 1 q 0 Kχ Ψ x f g
    _ ≤ _ := add_le_add hfull le_rfl

end
end ArtinMatthews
