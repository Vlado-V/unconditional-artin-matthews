module

public import ArtinMatthews.SourceKPIntertwinerRationalKernel
public import ArtinMatthews.SourceAdelicScalarHaar


set_option backward.privateInPublic true
@[expose] public section

/-! Rational-Borel invariance in the group variable of the actual
trace-Haar intertwining integral. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped NumberField MatrixGroups AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceRationalMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceRationalBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicTraceIntertwiner_rational_diagonal (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (a : Kˣ) :
    sourceKPAdelicTraceIntertwiner K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g) =
        sourceKPAdelicTraceIntertwiner K hζ s g := by
  unfold sourceKPAdelicTraceIntertwiner sourceKPAdelicIntertwiner
  simp_rw [sourceKPAdelicIntertwiningKernel_rational_diagonal]
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  have he : MeasurableEmbedding (fun y : 𝔸[K] =>
      algebraMap K 𝔸[K] (↑(a⁻¹) : K) * y) :=
    sourceKPAdelicPrincipalMul_measurableEmbedding K a⁻¹
  exact (sourceKPAdelicStandardHaar_principal_mul K a⁻¹).integral_comp he
    (sourceKPAdelicIntertwiningKernel K hζ s g)

theorem sourceKPAdelicTraceIntertwiner_rationalBorel (s : ℂ) (b : PGL(2, K))
    (hb : b ∈ sourceKPRationalBorel K) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ b * g) =
        sourceKPAdelicTraceIntertwiner K hζ s g := by
  have hb' : b ∈ sourceKPRingBorel K := by
    rw [sourceKPRingBorel_field]
    exact hb
  obtain ⟨x, a, hba⟩ := (sourceKPRingBorel_mem_iff K b).mp hb'
  have hu : sourceKPAdelicProjectiveRationalLift K hζ
      (ProjGenLinGroup.mk (sourceKPUpperMatrix K x)) =
        sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) := by
    rw [sourceKPUpperMatrix_field]
    exact (sourceKPAdelicUpperLift_rational K hζ x).symm
  rw [hba, map_mul, mul_assoc, hu, sourceKPAdelicTraceIntertwiner_left_upper,
    sourceKPAdelicTraceIntertwiner_rational_diagonal]

def sourceKPAdelicTraceIntertwiner_asRationalBorelFunction (s : ℂ) :
    SourceKPRationalBorelFunction K hζ :=
  ⟨sourceKPAdelicTraceIntertwiner K hζ s,
    sourceKPAdelicTraceIntertwiner_rationalBorel K hζ s⟩

theorem sourceKPAdelicTraceIntertwiner_asRationalBorelFunction_apply
    (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicTraceIntertwiner_asRationalBorelFunction K hζ s).val g =
      sourceKPAdelicTraceIntertwiner K hζ s g := rfl

end
end ArtinMatthews
