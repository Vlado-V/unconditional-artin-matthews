module

public import ArtinMatthews.StandardAdelicCharacterData
public import ArtinMatthews.SourceAdelicTraceHaar


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine negative trace character at a nonzero rational
frequency. Multiplication by the rational unit transports the actual
standard character, including its nontriviality. -/

namespace ArtinMatthews
open NumberField StandardAdelic
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPTraceJacquetCharacter (m : Kˣ) (y : 𝔸[K]) : ℂ :=
  star (StandardAdelic.character K (algebraMap K 𝔸[K] (m : K) * y))

theorem sourceKPTraceJacquetCharacter_add (m : Kˣ) (y z : 𝔸[K]) :
    sourceKPTraceJacquetCharacter K m (y+z) =
      sourceKPTraceJacquetCharacter K m y * sourceKPTraceJacquetCharacter K m z := by
  simp only [sourceKPTraceJacquetCharacter, mul_add, AddChar.map_add_eq_mul, star_mul']

theorem sourceKPTraceJacquetCharacter_continuous (m : Kˣ) :
    Continuous (sourceKPTraceJacquetCharacter K m) :=
  continuous_star.comp ((character_continuous K).comp (continuous_const.mul continuous_id))

theorem sourceKPTraceJacquetCharacter_norm (m : Kˣ) (y : 𝔸[K]) :
    ‖sourceKPTraceJacquetCharacter K m y‖ = 1 := by
  rw [sourceKPTraceJacquetCharacter, norm_star, character_unitary]

theorem sourceKPTraceJacquetCharacter_principal (m : Kˣ) (x : K) :
    sourceKPTraceJacquetCharacter K m (algebraMap K 𝔸[K] x) = 1 := by
  rw [sourceKPTraceJacquetCharacter, ← map_mul, character_principal, star_one]

theorem sourceKPTraceJacquetCharacter_rational_add (m : Kˣ) (x : K) (y : 𝔸[K]) :
    sourceKPTraceJacquetCharacter K m (y+algebraMap K 𝔸[K] x) =
      sourceKPTraceJacquetCharacter K m y := by
  rw [sourceKPTraceJacquetCharacter_add, sourceKPTraceJacquetCharacter_principal, mul_one]

theorem sourceKPTraceJacquetCharacter_nontrivial (m : Kˣ) :
    ∃ y : 𝔸[K], sourceKPTraceJacquetCharacter K m y ≠ 1 := by
  obtain ⟨z,hz⟩ := character_nontrivial K
  have hm : algebraMap K 𝔸[K] (m : K) * algebraMap K 𝔸[K] ((m⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨algebraMap K 𝔸[K] ((m⁻¹ : Kˣ) : K) * z, ?_⟩
  rw [sourceKPTraceJacquetCharacter, ← mul_assoc, hm, one_mul]
  intro h
  apply hz
  apply star_injective
  simpa only [star_one] using h

end
end ArtinMatthews
