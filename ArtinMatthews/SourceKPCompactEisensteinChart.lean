module

public import ArtinMatthews.SourceKPAdelicProductChartTopology
public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceKPCompactCoreCharts
public import ArtinMatthews.SourceKPArchHyperbolicMeasure
public import ArtinMatthews.SourceKPAutomorphicCompactEisenstein


set_option backward.privateInPublic true
@[expose] public section

/-! The literal full product Eisenstein chart is the pullback of the
actual compact-quotient Eisenstein function. -/

namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchUpperEuclidean_positive (p : SourceKPArchUpperHalfSpace K)
    (v : InfinitePlace K) : 0 < sourceKPArchUpperEuclideanMap K p v 2 :=
  sourceArchUpperEuclideanMap_positive (p v)

theorem sourceKPProductUpperCoordinates_euclidean (p : SourceKPArchUpperHalfSpace K) :
    sourceKPProductUpperCoordinates K
      ⟨sourceKPArchUpperEuclideanMap K p,sourceKPArchUpperEuclidean_positive K p⟩ = p := by
  let r := sourceKPArchUpperEuclideanMap K p
  calc
    _ = sourceKPArchEuclideanUpperMap K r := by
      funext v
      rw [sourceKPArchEuclideanUpperMap_positive K r (sourceKPArchUpperEuclidean_positive K p) v]
      apply Prod.ext
      · change (r v 0 : ℂ)+(r v 1 : ℂ)*Complex.I = (r v 0 : ℂ)+Complex.I*(r v 1 : ℂ)
        ring
      · rfl
    _ = p := sourceKPArchUpperEuclideanMap_left_inverse K p

theorem sourceKPArchUpperHalfspaceMatrix_euclidean (p : SourceKPArchUpperHalfSpace K) :
    sourceArchUpperHalfspaceMatrix K hζ (sourceKPArchUpperEuclideanMap K p)
      (sourceKPArchUpperEuclidean_positive K p) = sourceKPArchUpperHalfSection K hζ p := by
  let r : SourceKPProductUpper K :=
    ⟨sourceKPArchUpperEuclideanMap K p,sourceKPArchUpperEuclidean_positive K p⟩
  calc
    _ = sourceKPProductUpperSection K hζ r := (sourceKPProductUpperSection_eq K hζ r).symm
    _ = _ := congrArg (sourceKPArchUpperHalfSection K hζ)
      (sourceKPProductUpperCoordinates_euclidean K p)

theorem sourceKPUpperToCompact_section (qf : SourceKPFiniteAdeleProjective K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) p =
      sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        (ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ p),qf)) := by
  let a := ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ p)
  have hp : sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a) = p :=
    sourceKPArchSymmetricCoordinates_section K hζ p
  have he := sourceKPArithmeticUpperComponentHomeomorph_mk K hζ (QuotientGroup.mk qf) a
  rw [hp] at he
  exact he

theorem sourceKPAutomorphicCompactEisenstein_upper_chart (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPAutomorphicCompactEisenstein K hζ s
      (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) p) =
        sourceKPAdelicEisensteinProductChart K hζ s (1,qf) (sourceKPArchUpperEuclideanMap K p) := by
  rw [sourceKPUpperToCompact_section,sourceKPAutomorphicCompactEisenstein_adelic,
    sourceKPAdelicEisensteinProductChart,dite_eq_left (sourceKPArchUpperEuclidean_positive K p),
    sourceKPArchUpperHalfspaceMatrix_euclidean]
  congr 1
  exact Prod.ext (one_mul _).symm (mul_one _).symm

end
end ArtinMatthews
