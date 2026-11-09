module

public import ArtinMatthews.SourceKPTameBorelValues
public import ArtinMatthews.SourceKPProjectiveSections


set_option backward.privateInPublic true
@[expose] public section

/-! The actual spherical integrand on the local cubic cover, before
multiplication by the additive character. The change x = π^e H and
both Iwasawa branches are identities of the genuine section. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup AllowedGenerators
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "k₀" => sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆
local notation "ρ₀" => sourceKPTameBorelRepresentation K hζ P.val h₆ π₀ hπ₀
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

abbrev sourceKPTameExteriorSphericalSection :=
  sourceKPTameSphericalSection K hζ P.val h₆ π₀ hπ₀

local notation "f₀" => Subtype.val (sourceKPTameExteriorSphericalSection K hζ S₀ P)

def sourceKPTameJacquetPoint (e : ℤ) (x : L) : ZMod 3 → ℂ :=
  f₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x) * l₀ (sourceGL2Diagonal (π₀ ^ e)))

theorem sourceKPTameJacquetPoint_mul_uniformizer (e : ℤ) (H : L) :
    sourceKPTameJacquetPoint K hζ S₀ P e ((π₀ : L) ^ e * H) =
      ρ₀ (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (π₀ ^ (-e)))
        (f₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper H))) := by
  have hx : ((π₀ : L) ^ e * H) / ((π₀ ^ e : Lˣ) : L) = H := by
    rw [Units.val_zpow_eq_zpow_val, mul_div_cancel_left₀ _ (zpow_ne_zero _ (Units.ne_zero π₀))]
  rw [sourceKPTameJacquetPoint, mul_assoc, sourceFiniteKP2ProjectiveLift_upper_diagonal,
    hx, ← mul_assoc, sourceFiniteKP2ProjectiveLift_weyl_diagonal, mul_assoc, ← _root_.zpow_neg,
    ← sourceFiniteKPProjectiveBorelDiagonal_val]
  exact sourceKPTameSphericalSection_covariant K hζ P.val h₆ π₀ hπ₀ _ _

theorem sourceKPTameExteriorSpherical_weyl_upper_integral (H : L) (hH : ν₀ H ≤ 1) :
    f₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper H)) = sourceJacquetBasis 0 := by
  let w : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Weyl, sourceKPIntegralMatrix_weyl ν₀⟩
  let n : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Upper H, sourceKPIntegralMatrix_upper ν₀ H hH⟩
  have hw : k₀ w = l₀ sourceGL2Weyl := congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val)
    (sourceFiniteKP2CompactSection_weyl K hζ P.val h₆)
  have hn : k₀ n = l₀ (sourceGL2Upper H) := congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val)
    (sourceFiniteKP2CompactSection_upper K hζ P.val h₆ H hH)
  rw [← hw, ← hn, ← map_mul]
  exact sourceKPTameSphericalSection_compact K hζ P.val h₆ π₀ hπ₀ (w * n)

theorem sourceKPTameJacquetPoint_scaled_integral (e : ℤ) (H : L) (hH : ν₀ H ≤ 1) :
    sourceKPTameJacquetPoint K hζ S₀ P e ((π₀ : L) ^ e * H) =
      sourceJacquetScale Q₀ ((e : ℝ) / 3) • sourceJacquetBasis ((-e : ℤ) : ZMod 3) := by
  rw [sourceKPTameJacquetPoint_mul_uniformizer, sourceKPTameExteriorSpherical_weyl_upper_integral K hζ S₀ P H hH,
    sourceKPTameBorelRepresentation_uniformizer_basis]
  simp only [Int.cast_neg, neg_neg, zero_add]

theorem sourceKPTameExteriorSpherical_weyl_upper_bruhat (H : Lˣ) (hH : ν₀ ((H : L)⁻¹) ≤ 1) :
    f₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (H : L))) =
      ρ₀ (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (sourceBruhatDiagonal H)) (sourceJacquetBasis 0) := by
  let x := (H : L)⁻¹
  let n : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Lower x, sourceKPIntegralMatrix_lower ν₀ x hH⟩
  have hn : k₀ n = l₀ (sourceGL2Lower x) :=
    sourceFiniteKP2ProjectiveCompactSection_lower K hζ P.val h₆ x hH
  rw [sourceFiniteKP2ProjectiveLift_weyl_upper, mul_assoc,
    ← sourceFiniteKPProjectiveBorelUpper_val, sourceKPTameSphericalSection_covariant,
    sourceKPTameBorelRepresentation_upper, ← sourceFiniteKPProjectiveBorelDiagonal_val,
    sourceKPTameSphericalSection_covariant, ← hn, sourceKPTameSphericalSection_compact]

end
end ArtinMatthews
