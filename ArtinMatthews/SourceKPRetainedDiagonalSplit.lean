module

public import ArtinMatthews.SourceKPRetainedSeedSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Split a diagonal into its retained and exterior unit parts. The
retained product carries the original Hilbert cocycle, while the two
disjoint parts multiply without a phase. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "Z" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "unitAt" => sourceKPRetainedUnitAt K

def sourceKPRetainedDiagonalPhase (a b : 𝔸ᶠ[K]ˣ) : rootsOfUnity 3 K :=
  sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] a) (sourceKPDiagonalHom 𝔸ᶠ[K] b)

theorem sourceKPRetainedDiagonalLift_mul_phase (a b : 𝔸ᶠ[K]ˣ) :
    D a * D b = Z (sourceKPRetainedDiagonalPhase K hζ a b) * D (a*b) := by
  let F := SourceKPFiniteAdeleCover K hζ
  let M := sourceKPFiniteAdeleProjectiveMk K hζ
  let A := sourceKPDiagonalHom 𝔸ᶠ[K]
  let p := sourceKPRetainedDiagonalPhase K hζ a b
  change M (⟨1,A a⟩ : F) * M (⟨1,A b⟩ : F) =
    M (sourceKPFiniteAdeleCenter K hζ p) * M (⟨1,A (a*b)⟩ : F)
  rw [← map_mul M, ← map_mul M]
  apply congrArg M
  apply SourceKPFiniteAdeleCover.ext
  · change 1*1*p = p*1*sourceKPAdeleMultiplier K hζ 1 (A (a*b))
    rw [sourceKPAdeleMultiplier_one_left, one_mul, one_mul, mul_one, mul_one]
  · change A a * A b = 1*A (a*b)
    rw [one_mul, map_mul]

theorem sourceKPRetainedDiagonalLift_mul_of_disjoint (a b : 𝔸ᶠ[K]ˣ)
    (h : ∀ P : Pr, unitAt P a = 1 ∨ unitAt P b = 1) :
    D a * D b = D (a*b) := by
  have hp : sourceKPRetainedDiagonalPhase K hζ a b = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro P
    rw [sourceKPAdeleLocalMultiplier_diagonal]
    change (sourceKPRootsTransport K hζ P).symm (sourceFiniteKPHilbert K hζ P (unitAt P a) (unitAt P b)^2) = 1
    rcases h P with hP | hP
    · rw [hP, (sourceFiniteKPHilbert K hζ P).map_one, MonoidHom.one_apply, one_pow, map_one]
    · rw [hP, (sourceFiniteKPHilbert K hζ P (unitAt P a)).map_one, one_pow, map_one]
  rw [sourceKPRetainedDiagonalLift_mul_phase, hp, map_one, one_mul]

def sourceKPRetainedUnitPart (S : Finset Pr) (a : 𝔸ᶠ[K]ˣ) : 𝔸ᶠ[K]ˣ :=
  sourceKPRetainedDiagonalUnit K S (fun P => unitAt P.val a)

def sourceKPRetainedExteriorUnitPart (S : Finset Pr) (a : 𝔸ᶠ[K]ˣ) : 𝔸ᶠ[K]ˣ :=
  a * (sourceKPRetainedUnitPart K S a)⁻¹

theorem sourceKPRetainedExteriorUnitPart_unitAt_mem (S : Finset Pr) (a : 𝔸ᶠ[K]ˣ) (P : S) :
    unitAt P.val (sourceKPRetainedExteriorUnitPart K S a) = 1 := by
  rw [sourceKPRetainedExteriorUnitPart, map_mul, map_inv, sourceKPRetainedUnitPart,
    sourceKPRetainedDiagonalUnit_unitAt_mem, mul_inv_cancel]

theorem sourceKPRetainedExteriorUnitPart_unitAt_notMem (S : Finset Pr) (a : 𝔸ᶠ[K]ˣ) (P : Pr) (hP : P ∉ S) :
    unitAt P (sourceKPRetainedExteriorUnitPart K S a) = unitAt P a := by
  rw [sourceKPRetainedExteriorUnitPart, map_mul, map_inv, sourceKPRetainedUnitPart,
    sourceKPRetainedDiagonalUnit_unitAt_notMem K S _ P hP, inv_one, mul_one]

theorem sourceKPRetainedDiagonalUnit_mul (S : Finset Pr)
    (z w : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceKPRetainedDiagonalUnit K S z * sourceKPRetainedDiagonalUnit K S w =
      sourceKPRetainedDiagonalUnit K S (fun P => z P * w P) := by
  unfold sourceKPRetainedDiagonalUnit
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  simp only [← sourceKPRetainedLocalUnitHom_apply, map_mul]

theorem sourceKPRetainedDiagonalLift_split (S : Finset Pr) (a : 𝔸ᶠ[K]ˣ) :
    D a = D (sourceKPRetainedUnitPart K S a) * D (sourceKPRetainedExteriorUnitPart K S a) := by
  rw [sourceKPRetainedDiagonalLift_mul_of_disjoint]
  · congr 1
    dsimp only [sourceKPRetainedExteriorUnitPart]
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  · intro P
    by_cases hP : P ∈ S
    · exact Or.inr (sourceKPRetainedExteriorUnitPart_unitAt_mem K S a ⟨P,hP⟩)
    · exact Or.inl (sourceKPRetainedDiagonalUnit_unitAt_notMem K S _ P hP)

theorem sourceKPRetainedExteriorDiagonal_commute (S : Finset Pr) (a : 𝔸ᶠ[K]ˣ)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    Commute (D (sourceKPRetainedExteriorUnitPart K S a)) (D (sourceKPRetainedDiagonalUnit K S z)) := by
  have h (P : Pr) :
      unitAt P (sourceKPRetainedExteriorUnitPart K S a) = 1 ∨
      unitAt P (sourceKPRetainedDiagonalUnit K S z) = 1 := by
    by_cases hP : P ∈ S
    · exact Or.inl (sourceKPRetainedExteriorUnitPart_unitAt_mem K S a ⟨P,hP⟩)
    · exact Or.inr (sourceKPRetainedDiagonalUnit_unitAt_notMem K S z P hP)
  change D (sourceKPRetainedExteriorUnitPart K S a) * D (sourceKPRetainedDiagonalUnit K S z) =
    D (sourceKPRetainedDiagonalUnit K S z) * D (sourceKPRetainedExteriorUnitPart K S a)
  rw [sourceKPRetainedDiagonalLift_mul_of_disjoint K hζ _ _ h,
    sourceKPRetainedDiagonalLift_mul_of_disjoint K hζ _ _ (fun P => (h P).symm), mul_comm]

theorem sourceKPRetainedExteriorUnit_mul_upperSum (S : Finset Pr) (a : 𝔸ᶠ[K]ˣ)
    (u : ∀ P : S, P.val.adicCompletion K) :
    (sourceKPRetainedExteriorUnitPart K S a : 𝔸ᶠ[K]) *
        (∑ P : S, sourceKPFiniteAdditiveSingle K P.val (u P)) =
      ∑ P : S, sourceKPFiniteAdditiveSingle K P.val (u P) := by
  apply FiniteAdeleRing.ext
  intro P
  change (sourceKPRetainedExteriorUnitPart K S a : 𝔸ᶠ[K]) P *
    (∑ Q : S, sourceKPFiniteAdditiveSingle K Q.val (u Q)) P =
      (∑ Q : S, sourceKPFiniteAdditiveSingle K Q.val (u Q)) P
  by_cases hP : P ∈ S
  · have h := congrArg Units.val (sourceKPRetainedExteriorUnitPart_unitAt_mem K S a ⟨P,hP⟩)
    change (sourceKPRetainedExteriorUnitPart K S a : 𝔸ᶠ[K]) P = 1 at h
    rw [h, one_mul]
  · rw [sourceKPRetainedUpperSum_apply_notMem K S u P hP, mul_zero]

end
end ArtinMatthews
