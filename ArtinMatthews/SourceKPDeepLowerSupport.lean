module

public import ArtinMatthews.SourceKPDeepLowerMatrix
public import ArtinMatthews.SourceFiniteKPProjectiveBorel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact lower-root support of the actual deep compact model,
first in PGL2 and then in the genuine projective cubic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "O" => P.adicCompletionIntegers K
local notation "L" => P.adicCompletion K
local notation "D₀" => sourceKPDeepIntegralGroup K P

theorem sourceKPDeepLower_projective_iff (x : L) :
    (∃ (b : sourceGL2NormalizedBorel L) (k : D₀),
      ProjGenLinGroup.mk (sourceGL2Lower x) =
        ProjGenLinGroup.mk b.val * ProjGenLinGroup.mk (sourceKPDeepLocalBase K P k)) ↔
      x ∈ sourceKPDeepIdealImage K P := by
  constructor
  · rintro ⟨b, k, h⟩
    rw [← map_mul] at h
    obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
    have h10 : x * (a : L) = sourceKPDeepLocalBase K P k 1 0 := by
      calc
        _ = (sourceGL2Lower x * GeneralLinearGroup.scalar (Fin 2) a) 1 0 := by
          rw [sourceKPMatrix_right_scalar_entry]
          rfl
        _ = (b.val * sourceKPDeepLocalBase K P k) 1 0 :=
          congrArg (fun g : GL (Fin 2) L => g 1 0) ha
        _ = _ := by
          rw [sourceGL2_bottom_left_mul, b.property.1, b.property.2]
          ring
    have h11 : (a : L) = sourceKPDeepLocalBase K P k 1 1 := by
      calc
        _ = (sourceGL2Lower x * GeneralLinearGroup.scalar (Fin 2) a) 1 1 := by
          rw [sourceKPMatrix_right_scalar_entry]
          change (a : L) = 1 * (a : L)
          rw [one_mul]
        _ = (b.val * sourceKPDeepLocalBase K P k) 1 1 :=
          congrArg (fun g : GL (Fin 2) L => g 1 1) ha
        _ = _ := by
          rw [sourceGL2_bottom_right_mul, b.property.1, b.property.2]
          ring
    have hr := sourceKPDeepLocalBase_bottom_ratio K P k
    have he : sourceKPDeepLocalBase K P k 1 0 / sourceKPDeepLocalBase K P k 1 1 = x := by
      apply (div_eq_iff (sourceKPDeepLocalBase_bottomRight_ne_zero K P k)).mpr
      rw [← h11]
      exact h10.symm
    rwa [he] at hr
  · rintro ⟨r, hr, hrx⟩
    refine ⟨1, sourceKPDeepLower K P r hr, ?_⟩
    change ProjGenLinGroup.mk (sourceGL2Lower x) =
      ProjGenLinGroup.mk (1 : GL (Fin 2) L) *
        ProjGenLinGroup.mk (sourceKPDeepLocalBase K P (sourceKPDeepLower K P r hr))
    rw [map_one, one_mul, sourceKPDeepLocalBase_lower, hrx]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPDeepProjectiveSection : D₀ →* SourceFiniteKP2Projective K hζ P :=
  (sourceFiniteKP2ProjectiveMk K hζ P).comp (sourceKPDeepLocalSection K P hζ)

theorem sourceKPDeepProjectiveSection_projection (k : D₀) :
    sourceFiniteKP2ProjectiveProjection K hζ P (sourceKPDeepProjectiveSection K P hζ k) =
      ProjGenLinGroup.mk (sourceKPDeepLocalBase K P k) := rfl

theorem sourceKPDeepLower_cover_iff (x : L) :
    (∃ (b : SourceFiniteKPProjectiveBorel K hζ P) (k : D₀),
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Lower x) =
        b.val * sourceKPDeepProjectiveSection K P hζ k) ↔
      x ∈ sourceKPDeepIdealImage K P := by
  constructor
  · rintro ⟨b, k, h⟩
    obtain ⟨b₀, hb₀⟩ := b.property
    apply (sourceKPDeepLower_projective_iff K P x).mp
    refine ⟨⟨b₀.val.base, b₀.property⟩, k, ?_⟩
    have hp := congrArg (sourceFiniteKP2ProjectiveProjection K hζ P) h
    rw [map_mul, ← hb₀] at hp
    exact hp
  · rintro ⟨r, hr, hrx⟩
    refine ⟨1, sourceKPDeepLower K P r hr, ?_⟩
    change sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Lower x) =
      1 * sourceFiniteKP2ProjectiveMk K hζ P
        (sourceKPDeepLocalSection K P hζ (sourceKPDeepLower K P r hr))
    rw [one_mul, sourceKPDeepLocalSection_lower, hrx]
    rfl

end
end ArtinMatthews
