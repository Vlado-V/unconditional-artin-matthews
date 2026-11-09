module

public import ArtinMatthews.SourceKPLocalCompactGroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.SetTheory.Cardinal.Finite


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact cover has finitely many right deep-level
cosets. A representative consists of an integral matrix coset and
a central cube root, with the multiplication phase retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K
local notation "C" => sourceKPLocalCompactCover K hζ P
local notation "J" => sourceKPLocalCompactDeep K hζ P
local notation "J₀" => sourceKPDeepIntegralGroup K P
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "i₀" => sourceKPIntegralMatrixMap K P
local notation "D" => sourceKPLocalCompactDeepLift K hζ P
local notation "k₀" => sourceKPLocalCompactLift K hζ P

theorem sourceKPLocalCompactMatrixCosets_finite : Finite (GL (Fin 2) O ⧸ J₀) := by
  let : CompactSpace O := isCompact_iff_compactSpace.mp (sourceKPLocalIntegers_isCompact K P)
  let : CompactSpace (Matrix (Fin 2) (Fin 2) O) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → O))
  exact Subgroup.quotient_finite_of_isOpen J₀ (sourceKPDeepIntegralGroup_isOpen K P)

def sourceKPLocalCompactCosetMap :
    (rootsOfUnity 3 L × (GL (Fin 2) O ⧸ J₀)) → (C ⧸ J) :=
  fun (z,a) => QuotientGroup.mk (k₀ z a.out)

theorem sourceKPLocalCompactCosetMap_surjective :
    Function.Surjective (sourceKPLocalCompactCosetMap K hζ P) := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨z,a,rfl⟩ := sourceKPLocalCompactLift_surjective K hζ P g
  let c : GL (Fin 2) O ⧸ J₀ := QuotientGroup.mk a
  let a₀ := c.out
  have h : (QuotientGroup.mk a₀ : GL (Fin 2) O ⧸ J₀) = QuotientGroup.mk a :=
    QuotientGroup.out_eq' c
  let b : J₀ := ⟨a₀⁻¹*a,QuotientGroup.eq.mp h⟩
  have hb : a₀*b.val = a := mul_inv_cancel_left a₀ a
  let σ := sourceFiniteKP2Multiplier K hζ P (i₀ a₀) (i₀ b.val)
  have hmul : k₀ (z*σ⁻¹) a₀ * D b = k₀ z a := by
    apply Subtype.ext
    change (z₀ (z*σ⁻¹)*l₀ (i₀ a₀))*l₀ (i₀ b.val) = z₀ z*l₀ (i₀ a)
    rw [mul_assoc, sourceFiniteKP2ProjectiveLift_mul K hζ P, ← mul_assoc, ← map_mul]
    change z₀ ((z*σ⁻¹)*σ)*l₀ (i₀ a₀*i₀ b.val) = z₀ z*l₀ (i₀ a)
    rw [inv_mul_cancel_right, ← map_mul, hb]
  refine ⟨(z*σ⁻¹,c),?_⟩
  change (QuotientGroup.mk (k₀ (z*σ⁻¹) a₀) : C ⧸ J) = QuotientGroup.mk (k₀ z a)
  apply QuotientGroup.eq.mpr
  rw [← hmul, inv_mul_cancel_left]
  exact ⟨b,rfl⟩

theorem sourceKPLocalCompactCosets_finite : Finite (C ⧸ J) := by
  let : Finite (GL (Fin 2) O ⧸ J₀) := sourceKPLocalCompactMatrixCosets_finite K P
  exact Finite.of_surjective _ (sourceKPLocalCompactCosetMap_surjective K hζ P)

theorem sourceKPLocalCompactCosets_card_le :
    Nat.card (C ⧸ J) ≤ 3 * Nat.card (GL (Fin 2) O ⧸ J₀) := by
  let : Finite (GL (Fin 2) O ⧸ J₀) := sourceKPLocalCompactMatrixCosets_finite K P
  calc
    _ ≤ Nat.card (rootsOfUnity 3 L × (GL (Fin 2) O ⧸ J₀)) :=
      Nat.card_le_card_of_surjective _ (sourceKPLocalCompactCosetMap_surjective K hζ P)
    _ ≤ _ := by
      rw [Nat.card_prod]
      exact Nat.mul_le_mul_right _ (card_rootsOfUnity L 3)

theorem sourceKPLocalCompactDeep_projection_eq_one (a : J)
    (h : sourceFiniteKP2ProjectiveProjection K hζ P a.val.val = 1) : a = 1 := by
  obtain ⟨b,hb⟩ := a.property
  have hp : ProjGenLinGroup.mk (i₀ b.val) = 1 := by
    change sourceFiniteKP2ProjectiveProjection K hζ P (D b).val = 1
    rwa [hb]
  have hc := ProjGenLinGroup.mk_eq_one.mp hp
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨t,ht⟩ := hc
  apply Subtype.ext
  apply Subtype.ext
  change a.val.val = 1
  rw [← hb, sourceKPLocalCompactDeepLift_val K hζ P, ← ht]
  exact sourceFiniteKP2ProjectiveMk_scalar K hζ P t

end
end ArtinMatthews
